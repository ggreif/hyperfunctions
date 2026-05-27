module Constructor.Sort (Sort (..)) where

-- | Syntactic sort, used to index the finally-tagless carrier so that
--   one type-class can describe the whole grammar.
data Sort = SProg | SDecl | SExpr
