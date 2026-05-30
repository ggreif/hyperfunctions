{-# LANGUAGE DataKinds #-}

module Constructor.Sort
  ( Sort (..)
  , Mode (..)
  ) where

-- | Mode of a value-level term — whether it's being /assembled/
--   (constructed, the right-hand side of a let or a case arm) or
--   /dissected/ (matched against, the left-hand side of a case arm).
--   Patterns and values share a single AST sort 'SVal'; the @'Mode@
--   phantom is what statically distinguishes "this is a pattern" from
--   "this is a value expression" in the 'Lang' typeclass.
data Mode = Build | Dissect

-- | Syntactic sort, used to index the finally-tagless carrier so that
--   one type-class can describe the whole grammar.
--
--   'SExpr' covers type-level expressions (the @T@ in @c : T@).
--   'SVal m' covers value-level expressions in mode @m@: @SVal Build@
--   for assembling (the RHS of an arm; the body of a @let@) and
--   @SVal Dissect@ for dissecting (the LHS of an arm).  Bipartite
--   forms (ctor application, variable, literal, @at@-binder) are
--   parametric in @m@; mode-specific forms (wildcard '_', lambda,
--   nested case) instantiate @m@ to the appropriate value at their
--   'Lang'-method signature.  'SArm' covers one @pat -> body@.
data Sort = SProg | SDecl | SExpr | SVal Mode | SArm
