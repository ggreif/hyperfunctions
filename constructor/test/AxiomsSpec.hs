{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Axiomatic Build → Dissect → Build round-trip tests.
--
--   Each program builds a ctor-shaped value, dissects it with a
--   covering case, and rebuilds the scrutinee shape arm-by-arm.
--   The /axiomatic/ content the suite captures is:
--
--     1. **What can be built can be dissected.**  Every Built
--        value matches at least one arm (no inexhaustive matches).
--
--     2. **What is dissected can be rebuilt to the /same type/.**
--        The case as a whole types at the scrutinee's type — each
--        arm's body, after refinement, produces a value at that
--        type.  For refining GADTs (real Fin / Expr / Refl) some
--        arms become unreachable; the elaborator should accept
--        them anyway and the round-trip should still preserve
--        type at the reachable arm(s).
--
--   At this commit HypTwr does scope-only elaboration for value-
--   level terms — the tests confirm the programs parse + elaborate
--   without scope errors and that the expected 'let' binders land
--   in 'hypTwrValVars'.  When Build / Dissect type-checking lands
--   (next segment), the same programs will exercise real
--   refinement unification; tests that today are weak (scope-only)
--   strengthen automatically because 'hypTwrProgram' starts
--   inspecting types as well as scope.
module AxiomsSpec (tests) where

import Constructor.HypTwr (HypTwr, HypTwrResult (..), hypTwrProgram)
import Constructor.Parser (parseProgram)
import Constructor.Syntax (Name)
import Constructor.Tower (Tower (..))
import Constructor.TyExpr (prettyTy)
import Constructor.TyProc (materialize)
import Data.Functor.Const (Const (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec (errorBundlePretty)

tests :: [(String, IO Bool)]
tests =
  [ -- --- Non-refining round-trips -----------------------------------
    --
    -- Bool and Nat: no per-ctor refinement; every arm's pattern
    -- and body share the same shape, so Build → Dissect → Build is
    -- trivially type-preserving.  Scope axioms:
    --
    --   * Built value's name is bound for the case to consume.
    --   * Each arm's pattern-introduced binder is in scope in its
    --     body and resolves through HypTwr.
    --   * Rebuilding the same ctor shape on the RHS doesn't escape
    --     the arm — bound names are arm-local, but the rebuilt
    --     value's typing context is the case's outer scope.

    roundTripVia "Bool round-trip: case T { T -> T; F -> F }"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let rt = case T { T -> T; F -> F }"
      [("rt", "Bool")]

  , roundTripVia "Nat round-trip: case S Z { Z -> Z; S n -> S n }"
      -- Round-trip preserves ctor shape under FS-binding.  The
      -- pattern binder 'n' flows from the FS pattern into the FS
      -- argument position on the RHS; the rebuilt value has the
      -- same Nat shape the scrutinee had.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let rt = case S Z { Z -> Z; S n -> S n }"
      [("rt", "Nat")]

    -- --- Refining round-trips -----------------------------------------
    --
    -- Real Fin: per-ctor result refinement.  The 'FZ' arm refines
    -- 'n' to 'Z'; the 'FS m' arm refines 'n' to 'S m' with 'm' a
    -- fresh existential.  For a scrutinee of type 'Fin (S Z)':
    --
    --   * The 'FZ' arm is /unreachable/ (refinement clash:
    --     'S Z != Z'), but the elaborator accepts the arm —
    --     unreachability is a coverage observation, not a type
    --     error.
    --   * The 'FS m' arm is reachable; 'm := Z' instantiates the
    --     existential.  Rebuilding 'FS m' yields 'Fin (S m) =
    --     Fin (S Z)' — same type as the scrutinee.
    --
    -- Today: scope-only.  When pat refinement lands, the test
    -- strengthens automatically into a genuine refinement axiom.

  , roundTripVia "Fin round-trip: case FS FZ { FZ -> FZ; FS m -> FS m }"
      -- Refining GADT round-trip — the load-bearing case.
      -- Scrutinee @FS FZ@ has type @Fin (S Z)@.  The @FZ@ arm's
      -- pattern matches @Fin Z@; refinement clashes with the
      -- scrutinee's @Fin (S Z)@, so HypTwr marks the arm
      -- /unreachable/ and skips its body when meeting per-arm
      -- result types.  The @FS m@ arm refines @m@ to @Z@ and
      -- its body @FS m@ rebuilds at @Fin (S Z)@ — same type
      -- as the scrutinee.  The axiom holds.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let rt = case FS FZ { FZ -> FZ; FS m -> FS m }"
      [("rt", "Fin (S Z)")]

    -- --- Typed-AST round-trip ----------------------------------------
    --
    -- Real Expr from GadtSpec: 'Lit : Expr T', 'Pair : Expr T ->
    -- Expr F -> Expr F'.  Round-tripping 'Lit' through its arm
    -- preserves the 'Expr T' result type.  The 'Pair l r' arm's
    -- pattern binders 'l' and 'r' flow into the rebuilt 'Pair l r'.

  , roundTripVia "Expr round-trip: case Lit { Lit -> Lit }"
      "data Bool : *0 { T : Bool; F : Bool };\
      \data Expr (a : Bool) : *0 { Lit : Expr T; Pair : Expr T -> Expr F -> Expr F };\
      \let rt = case Lit { Lit -> Lit; Pair l r -> Lit }"
      [("rt", "Expr T")]

    -- --- Coverage axiom: every Built value matches an arm --------
    --
    -- This test will tighten when coverage checking is added.
    -- Today it just confirms that all reachable arms parse + scope.
    -- A future commit lands inexhaustive-match detection on top.

  , roundTripVia "Coverage: every Bool-ctor has a covering arm"
      "data Bool : *0 { T : Bool; F : Bool };\
      \let cov = case T { T -> F; F -> T }"
      [("cov", "Bool")]

    -- --- Weird-class (self-towering / singleton family) -----------
    --
    -- Singleton self-towering data have each ctor's annotation
    -- equal to its own name (or another sibling's): the value
    -- 'One' has type 'One', not 'Iso'.  At case time the
    -- scrutinee's type is fixed by /which/ ctor built it, so
    -- only that arm's pattern meets the scrutinee — every other
    -- arm clashes on TyMismatch and is filtered.  Reachable
    -- arms agree on their rebuild type (= scrutinee's type) by
    -- construction.
    --
    -- The covering-space framing's content surfaces here: at a
    -- nullary self-towering parent, the parent and each ctor
    -- inhabit the same parametric-level fibre, and the
    -- value-level Build / Dissect pas-de-deux is just the
    -- TyConV identity check.

  , roundTripVia "Weird round-trip: case Level0 { Level0 -> Level0 }"
      -- The minimal Weird-class case: one ctor, one arm.  Scrut
      -- @Level0 : Weird@; pat @Level0@ tower @Weird@ meets;
      -- body @Level0@ rebuilds at @Weird@ — same type as the
      -- scrutinee.
      "data Weird : Weird { Level0 : Weird };\
      \let rt = case Level0 { Level0 -> Level0 }"
      [("rt", "Weird")]

  , roundTripVia "Iso round-trip: case One { One -> One; Two -> Two; Three -> Three }"
      -- The Iso-cute singleton: each ctor has its own type.
      -- For scrut @One : One@, arm @One@ tower @One@ meets;
      -- arms @Two@ and @Three@ have towers @Two@ / @Three@ —
      -- both clash with @One@, both filtered.  Reachable arm's
      -- body @One@ rebuilds at @One@ = scrutinee's type.
      "data Iso : Iso { One : One; Two : Two; Three : Three };\
      \let rt = case One { One -> One; Two -> Two; Three -> Three }"
      [("rt", "One")]

  , roundTripVia "Swap round-trip: case Left { Left -> Left; Right -> Right }"
      -- Swap's twist: @Left@'s annotation is @Right@ (and vice
      -- versa).  So @Left@ /builds/ a value of type @Right@.
      -- Scrut @Left : Right@; arm @Left@'s pat tower is also
      -- @Right@ (matching the building-rule); arm @Right@'s pat
      -- tower is @Left@ — clashes with @Right@, filtered.
      -- Body @Left@ rebuilds at @Right@.  The round-trip's
      -- typed shape is /the swap target/, not the matched ctor.
      "data Swap : Swap { Left : Right; Right : Left };\
      \let rt = case Left { Left -> Left; Right -> Right }"
      [("rt", "Right")]

  , roundTripVia "Mirror round-trip: case Cup { Cup -> Cup; Fridge -> Fridge; Plate -> Plate }"
      -- The universe-polymorphic Iso: same structure as Iso
      -- but the parent's kind is @∀l. *l@ rather than a
      -- self-referential TyConRef.  Cup/Fridge/Plate live at
      -- the parametric level the parent's ∀ introduces.  At
      -- value level the type-checker doesn't care about the
      -- parent's level shape — the case operates on TyConV
      -- identity of each ctor's annotation, exactly as in Iso.
      "data Mirror : \8704l. *l { Cup : Cup; Fridge : Fridge; Plate : Plate };\
      \let rt = case Cup { Cup -> Cup; Fridge -> Fridge; Plate -> Plate }"
      [("rt", "Cup")]

    -- --- @-pattern round-trips: genuine identity through dissect -----
    --
    -- The earlier round-trips smuggle a rebuild past the dissect:
    -- @case One { One -> One; ... }@ matches a value of type
    -- @One@ and then /builds a fresh One/ on the body side — no
    -- "part" flows through the bridge.  @-binders fix this: the
    -- body returns the at-bound name, which IS the scrutinee's
    -- matched value (modulo the type-level representation).
    -- Dissect → bind → carry over → identity-rebuild.

  , roundTripVia "@-round-trip: case One { y@One -> y; y@Two -> y; y@Three -> y }"
      -- Each arm's pattern @y\@<ctor>@ binds the matched value
      -- to @y@; the body returns @y@ rather than synthesising
      -- a fresh ctor.  For scrut @One@ only the first arm is
      -- reachable; @y@ binds at @One@, body returns @One@.
      "data Iso : Iso { One : One; Two : Two; Three : Three };\
      \let rt = case One { y@One -> y; y@Two -> y; y@Three -> y }"
      [("rt", "One")]

  , roundTripVia "@-round-trip: Nat with at-binder on S-arm"
      -- The @S y@S n -> y@-shape: matches a Nat that's a
      -- successor of a successor; binds @y@ to the inner
      -- @S n@ (a Nat); body returns @y@.  For scrut
      -- @S (S Z)@ the second arm is reachable; @y@ is the
      -- /inner/ @S Z@ — not the whole scrutinee — and the
      -- result type is Nat.  Note: no parens needed around
      -- @S n@ on the LHS — application binds tighter than
      -- '@', so @y@S n@ parses as @y@(S n)@.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \let rt = case S (S Z) { Z -> Z; S y@S n -> y; S Z -> Z }"
      [("rt", "Nat")]

  , roundTripVia "@-round-trip: Fin refinement via at-bound whole"
      -- Genuine refining-GADT round-trip via at-binder.  Scrut
      -- @FS FZ : Fin (S Z)@; arm @y@FS m -> y@ binds @y@ to
      -- the matched value, which has type @Fin (S Z)@ (after
      -- Dissect-side refinement unifies the pattern's
      -- @Fin (S α)@ with the scrutinee's @Fin (S Z)@).  Body
      -- returns @y@, a real "carry the dissected value across"
      -- (no rebuild from parts).  No parens around @FS m@: '@'
      -- captures the largest application to its right.
      "data Nat : *0 { Z : Nat; S : Nat -> Nat };\
      \data Fin (n : Nat) : *0 { FZ : Fin Z; FS : Fin n -> Fin (S n) };\
      \let rt = case FS FZ { y@FZ -> y; y@FS m -> y }"
      [("rt", "Fin (S Z)")]

    -- --- Existential round-trips -------------------------------------
    --
    -- A ctor whose argument-side carries an existentially-bound
    -- type variable: @Pack : ∃ m. m -> Foo@.  At each Build site
    -- @m@ gets a fresh meta — instantiated to whatever the arg's
    -- type happens to be — but the result type is just @Foo@,
    -- with @m@ hidden.  The pattern-match arm gets a fresh skolem
    -- for the existential; the rebuilt value's @Foo@ doesn't
    -- expose it.  The axiom: the round-trip preserves @Foo@
    -- regardless of what type the existential was instantiated to
    -- at the original Build site.

  , roundTripVia "Existential round-trip: case Pack T { Pack x -> Pack x }"
      -- Build @Pack T@: existential @m@ instantiated to @Bool@
      -- (T's type), result @Foo@.  Pattern-match: @x@ bound at
      -- a fresh meta, the @Pack x@ pat-tower @Foo@ meets the
      -- scrutinee's @Foo@.  Body rebuilds @Pack x@ at @Foo@.
      "data Bool : *0 { T : Bool };\
      \data Foo : *0 { Pack : \8707 m . m -> Foo };\
      \let rt = case Pack T { Pack x -> Pack x }"
      [("rt", "Foo")]
  ]

-- | Parse → 'HypTwr' → expect success.  For each expected let
--   binder, look up its tower in 'hypTwrValVars', materialise
--   the first rung through the result's 'Subst', and compare
--   the pretty-rendered type against the expected text.
--
--   This is what makes the round-trip an /axiom/: the case-as-
--   a-whole is type-checked, the case's result type is the let
--   binder's type, and we assert it equals the expected text.
--   For Build → Dissect → Build round-trips the expected text
--   is the scrutinee's type — the literal "Built can be Dissected
--   and rebuilt to the same type" invariant.
roundTripVia :: String -> Text -> [(Name, Text)] -> (String, IO Bool)
roundTripVia name src wantLetTypes = (name, go)
  where
    go = case parseProgram @HypTwr @(Const ()) name src of
      Left e -> fail_ $ "parse error: " <> errorBundlePretty e
      Right pTwr -> case hypTwrProgram pTwr of
        Left ty -> fail_ $ "HypTwr rejected: " <> show ty
        Right r ->
          let subst   = hypTwrSubst r
              valVars = hypTwrValVars r
              errs    = concatMap (checkOne subst valVars) wantLetTypes
          in if null errs
               then pure True
               else fail_ (unlines errs)

    checkOne subst valVars (n, wantPretty) =
      case Map.lookup n valVars of
        Nothing -> ["binder not found: " <> show n]
        Just tower -> case materialize subst (horizontal tower) of
          Left err -> ["materialise failed for " <> show n <> ": " <> show err]
          Right ty ->
            let got = prettyTy ty
            in if got == wantPretty
                 then []
                 else
                   [ "type mismatch for " <> show n <> ":"
                   , "  want: " <> T.unpack wantPretty
                   , "  got:  " <> T.unpack got
                   ]

    fail_ msg = putStrLn ("    " <> msg) >> pure False
