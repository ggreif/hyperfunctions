{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- | A Haskell-source-emitting 'Lang' carrier.  Each method writes a
--   text fragment; 'prog' assembles them into a compilable module
--   you can pipe into @runghc@.
--
--   Intended use:
--
-- @
--   case parseProgram @Hs @(Const ()) "demo" src of
--     Right pHs -> putStrLn (renderHs pHs)
-- @
--
--   …or pipe the output to ghc to confirm that GHC accepts the
--   translation.  Ωmegator's '@' is greedy (application binds
--   tighter); Haskell's is the opposite, so 'valAt' emits parens
--   around the inner to satisfy GHC.  Other surface asymmetries
--   are similarly bridged at the carrier boundary: universe
--   annotations are dropped (Haskell collapses our level
--   distinction to a single @Type@), every @data@ uses GADT
--   @where@-syntax (uniform; the parametric ones need it, the
--   non-parametric ones tolerate it), and standalone
--   @deriving Show@ instances are emitted alongside each data so
--   the @main = print rt@ entry point works for any program
--   whose load-bearing binder is called @rt@.
--
--   /Just enough/ to round-trip the Fin GADT demo end-to-end; the
--   carrier crashes on syntactic features the demo doesn't use
--   ('valWild', 'forallLv', 'existsTy', 'starVar') — those land
--   when an Ωmegator example actually needs them.
module Constructor.Hs
  ( Hs (..)
  , renderHs
  ) where

import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..))
import Data.Kind (Type)
import qualified Data.Text as T

-- | Haskell-source fragment, indexed by sort for type-safety of
--   the 'Lang' instance.  Sort phantom; the payload is a 'String'
--   for either an expression, a declaration, or a whole module.
newtype Hs (a :: Sort -> Type) (s :: Sort) = Hs { unHs :: String }

renderHs :: Hs a 'SProg -> String
renderHs = unHs

instance Lang Hs where
  prog _ann ds = Hs $ unlines $
    [ "{-# LANGUAGE NoImplicitPrelude #-}"
    , "{-# LANGUAGE DataKinds #-}"
    , "{-# LANGUAGE GADTs #-}"
    , "{-# LANGUAGE KindSignatures #-}"
    , "{-# LANGUAGE StandaloneDeriving #-}"
    , ""
    , "module Main where"
    , ""
    -- 'NoImplicitPrelude' frees Bool / True / False / Maybe / ...
    -- and any other Prelude name for Ωmegator-side reuse without
    -- clash.  We only need IO / print / Show for 'main = print rt'
    -- and the standalone Show instances each data emits.
    , "import Prelude (IO, print, Show)"
    , ""
    ] ++ map unHs ds ++
    [ ""
    , "main :: IO ()"
    , "main = print rt"
    ]

  -- Every data emits GADT-style @data X (a :: K) ... where ...@:
  -- non-parametric data (Nat, Bool) tolerate this form; parametric
  -- refining data (Fin) need it.  Universe annotation dropped —
  -- Haskell collapses our level distinction to 'Type'.  A standalone
  -- 'deriving Show' instance is emitted alongside each so 'print'
  -- works at top level.
  dataDecl _ann _declPath name params _kindExpr ctors = Hs $
    let nameStr  = T.unpack name
        paramStr = case params of
          [] -> ""
          ps -> ' ' : unwords (map paramStrOne ps)
        ctorStrs = map unHs ctors
    in "data " <> nameStr <> paramStr <> " where\n"
       <> concatMap (\s -> "  " <> s <> "\n") ctorStrs
       <> "\nderiving instance Show (" <> nameStr <> paramStr <> ")\n"
    where
      paramStrOne (n, Just kindHs) =
        "(" <> T.unpack n <> " :: " <> unHs kindHs <> ")"
      paramStrOne (n, Nothing)     = T.unpack n

  ctorDecl _ann name ty = Hs $ T.unpack name <> " :: " <> unHs ty

  -- Type-level expressions:

  var        _ann n         = Hs (T.unpack n)
  tyParamRef _ann n _path   = Hs (T.unpack n)
  tyConRef   _ann n _path   = Hs (T.unpack n)
  star       _ann _w        = Hs "Type"
  arr _ann a b              = Hs (unHs a <> " -> " <> unHs b)
  app _ann _appPath f x     = Hs (unHs f <> " " <> parensIf x)

  -- Value-level expressions:

  valDecl _ann _declPath name body = Hs $
    T.unpack name <> " = " <> unHs body <> "\n"
  valVar  _ann n _path   = Hs (T.unpack n)
  valCtor _ann name _path args = Hs $ case args of
    [] -> T.unpack name
    _  -> T.unpack name <> " " <> unwords (map parensIf args)
  case_ _ann scrut arms = Hs $
    "case " <> unHs scrut <> " of\n"
    <> unlines [ "    " <> unHs a | a <- arms ]
  arm _ann pat body = Hs (unHs pat <> " -> " <> unHs body)

  -- @-binder: Haskell's '@' binds tighter than application (the
  -- opposite of our greedy rule), so the inner needs parens for
  -- ctor-app shapes.  Always emitting parens is safe and uniform.
  valAt _ann name _bp inner = Hs $
    T.unpack name <> "@(" <> unHs inner <> ")"

-- | Wrap a fragment in parens if it would otherwise lose its grouping
--   when placed in argument position.  Crude heuristic — any
--   whitespace means "compound".  Sufficient for the AxiomsSpec
--   corpus.
parensIf :: Hs a s -> String
parensIf (Hs s)
  | any (== ' ') s = "(" <> s <> ")"
  | otherwise      = s
