{-# LANGUAGE OverloadedStrings #-}

-- | Value-level interpreter for the constructor language.
--
--   A small reduction engine for the value-level fragment: variables,
--   ctor applications, lambdas, case expressions.  Produces a normal
--   form (a 'Value') or a stuck term when reduction can't proceed.
--
--   Phase B of the narrowing plan ('.claude/plans/narrowing.md'):
--   standalone module, not yet wired into HypTwr.  Phase C will hook
--   this from HypTwr's 'meet' when a 'TyDeferV' application appears
--   with all-concrete args.  Phase D will extend it with narrowing
--   (case-split on stuck head metas via LogicT).
--
--   For now: pure structural reduction, no metas, no narrowing.
module Constructor.Interp
  ( -- * IR
    Expr (..)
  , Pattern (..)
  , Arm (..)
    -- * Values
  , Value (..)
  , Stuck (..)
    -- * Reduction
  , interp
  , Env
  , Globals
  ) where

import Constructor.Syntax (Name)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Value-level expression — a simplified IR for the interpreter.
--   Built from the constructor's 'Tree' AST by an upcoming carrier
--   (or hand-constructed for testing).
data Expr
  = EVar !Name
  | ECtor !Name ![Expr]
  | ELam !Name !Expr
  | EApp !Expr !Expr
  | ECase !Expr ![Arm]
  deriving (Eq, Show)

-- | Patterns appearing in case arms.
data Pattern
  = PVar !Name
  | PCtor !Name ![Pattern]
  | PWild
  | PAt !Name !Pattern   -- @-binder: name@inner; binds name to the whole
                          --   matched value AND recurses into inner.
  deriving (Eq, Show)

-- | One arm of a case expression.
data Arm = Arm !Pattern !Expr
  deriving (Eq, Show)

-- | A reduced value, or a stuck term.  The two are distinguished by
--   constructor: 'VCon'/'VClos' are reduced; 'VStuck' carries the
--   stuck-shape so callers (Phase D narrowing) can decide what to
--   do.
data Value
  = VCon !Name ![Value]
  | VClos !Env !Name !Expr
  | VStuck !Stuck
  deriving (Eq, Show)

-- | A stuck term.  Reduction halted because the head can't be reduced
--   (a free variable, a stuck application, a case on a stuck
--   scrutinee).  At Phase B these are just observed and returned;
--   Phase D will case-split on 'SCase' with a 'VCon'-ctor scrutinee.
data Stuck
  = SVar !Name
  | SApp !Value !Value
  | SCase !Value ![Arm]
  deriving (Eq, Show)

-- | Lexical environment: name-to-value bindings introduced by lambdas
--   and pattern-binders.
type Env = Map Name Value

-- | Top-level definitions: name-to-Expr bindings for the program's
--   let-decls.  Looked up by 'EVar' when the env doesn't have the
--   name locally.
type Globals = Map Name Expr

-- | The reduction engine.  Walks the expression, reducing applications
--   against closures, dispatching cases against ctor scrutinees, and
--   chasing variables through the env-then-globals lookup chain.
--
--   Produces a 'Value' that is either:
--
--     * 'VCon n args' — a normal ctor value (args are also reduced),
--     * 'VClos env x body' — an unapplied closure (lambda),
--     * 'VStuck s' — reduction halted at an irreducible term.
interp :: Globals -> Env -> Expr -> Value
interp gs env e = case e of
  EVar n -> case Map.lookup n env of
    Just v  -> v
    Nothing -> case Map.lookup n gs of
      Just body -> interp gs Map.empty body
      Nothing   -> VStuck (SVar n)

  ECtor n args -> VCon n (map (interp gs env) args)

  ELam x body -> VClos env x body

  EApp f a -> case interp gs env f of
    VClos env' x body -> interp gs (Map.insert x va env') body
      where va = interp gs env a
    VCon n vs -> VCon n (vs <> [interp gs env a])
    VStuck s  -> VStuck (SApp (VStuck s) (interp gs env a))

  ECase scrut arms -> case interp gs env scrut of
    VCon sn sargs -> tryArms sn sargs arms
    other         -> VStuck (SCase other arms)
  where
    -- Try each arm against a fully-reduced ctor scrutinee.
    -- First match wins; binders introduced by the pattern flow
    -- into the body's env via 'matchPattern'.
    tryArms _  _     []                  = VStuck (SCase (VCon "<unreached>" []) [])
    tryArms sn sargs (Arm pat body : rest) =
      case matchPattern pat (VCon sn sargs) of
        Just bindings -> interp gs (bindings <> env) body
        Nothing       -> tryArms sn sargs rest

-- | Match a pattern against a value; on success, return the bindings
--   the pattern introduces.  'Nothing' means the pattern's shape
--   doesn't match (try the next arm).
matchPattern :: Pattern -> Value -> Maybe Env
matchPattern pat v = case (pat, v) of
  (PWild, _) -> Just Map.empty
  (PVar n, _) -> Just (Map.singleton n v)
  (PAt n inner, _) -> do
    innerBinds <- matchPattern inner v
    pure (Map.insert n v innerBinds)
  (PCtor pn ps, VCon vn vs)
    | pn == vn && length ps == length vs ->
        mconcat <$> traverse (uncurry matchPattern) (zip ps vs)
  _ -> Nothing
