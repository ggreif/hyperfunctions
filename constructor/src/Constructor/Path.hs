-- | Syntactic paths through the 'Lang' grammar.  Used to give each
--   binder a deterministic identity derived from its position in the
--   source — replacing the per-parse counter that previously
--   identified 'LVar's.
--
--   We do **not** path-combine (binder-path ⊕ use-path) because we
--   follow the SPJ "let should not be generalised" stance: every
--   polymorphic value is named via an explicit '∀', and there is no
--   multi-site instantiation of an implicitly-generalised let-binding.
--   Each '∀l.' has identity = its own path; every reference to 'l'
--   resolves to that same path.  When multi-site instantiation of
--   polymorphic data arrives (future), only THEN does the per-use
--   freshness matter and the combining trick re-enters.
module Constructor.Path
  ( PathStep (..)
  , Path (..)
  , emptyPath
  , extendPath
  ) where

-- | One descent in the grammar.
data PathStep
  = PsProgDecl  !Int   -- ^ nth top-level declaration in a program
  | PsDataAnn          -- ^ the universe annotation of a data declaration
  | PsDeclIdx   !Int   -- ^ nth inner declaration inside a data body
  | PsCtorTy           -- ^ the type of a constructor declaration
  | PsArrL             -- ^ left side of an arrow
  | PsArrR             -- ^ right side of an arrow
  | PsAppFun           -- ^ function position of an application
  | PsAppArg           -- ^ argument position of an application
  | PsForallBody       -- ^ the body of a '∀l.' expression
  | PsParens           -- ^ inside an explicit '(…)' grouping
  | PsDataParam !Int   -- ^ the nth type parameter of a data declaration (def-path)
  | PsDataParamKind !Int
                       -- ^ the kind annotation slot of the nth data parameter
                       --   (for @data Foo (a : K)@-style annotations).
  | PsExistsBody       -- ^ the body of a '∃ m.' expression (existential
                       --   type-variable binder introduced in a ctor type).
  | PsLetBody          -- ^ the RHS of a top-level @let name = body@
                       --   value declaration.
  | PsCaseScrut        -- ^ the scrutinee of a @case@ expression.
  | PsCaseArm   !Int   -- ^ the nth arm of a @case@.
  | PsArmPat           -- ^ the pattern (LHS of @->@) of one arm.
  | PsArmBody          -- ^ the body (RHS of @->@) of one arm.
  | PsCtorAppArg !Int  -- ^ the nth argument of a value-level ctor
                       --   application (Build or Dissect mode).
  | PsAtInner          -- ^ the inner pattern of an @-binder
                       --   @name\@<pat>@: 'PsAtInner' steps from
                       --   the outer at-position to its sub-pattern
                       --   so binders inside the inner get fresh
                       --   identities even when the at-binder
                       --   sits at the outer position itself.
  deriving (Eq, Ord, Show)

-- | A path from the root of the program to a particular grammar
--   position.  Stored root-to-leaf (newest step at the end) so
--   'extendPath' is a snoc.
newtype Path = Path { unPath :: [PathStep] }
  deriving (Eq, Ord, Show)

emptyPath :: Path
emptyPath = Path []

-- | Append a step to a path.
extendPath :: PathStep -> Path -> Path
extendPath step (Path steps) = Path (steps ++ [step])
