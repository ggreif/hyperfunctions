{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

-- | A Scott-encoding Haskell-source carrier of the 'Lang' algebra.
--
--   Where 'Constructor.Hs' emits straightforward Haskell @data@
--   declarations + @case … of@ expressions, 'Scott' emits the
--   Scott-encoded form: each Ωmegator data type becomes a single
--   eliminator @newtype X'@; each ctor becomes a lowercase function
--   that picks its branch position; each case is a direct
--   application of the scrutinee to per-arm branch lambdas.
--
--   /Just enough/ to round-trip the nullary-ctor demos (Bool, Iso).
--   Captured-args (Nat S) and refining GADTs (Fin) follow once the
--   simple shape is nailed down.
--
--   The carrier is stateful (a 'State' monad over an 'Env' tracking
--   data-to-ctor associations), so 'case_' can look up the
--   scrutinee's eliminator name from the ctor that built it.  The
--   alternative (impredicative-third-slot like HypLinf) was
--   considered and rejected as overkill for a sparse signal.
module Constructor.Scott
  ( Scott
  , renderScott
  ) where

import Constructor.Path (Path)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Control.Monad.State (State, evalState, gets, modify)
import Data.Char (toLower)
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

-- | Per-sort carrier output.  Some sorts carry extra metadata
--   beyond the emitted text — most importantly, 'SVal' carries
--   the value's "head ctor" (the outer ctor that built it, when
--   directly visible) so 'case_' can look up the right
--   eliminator function from the env.
data ScottOut (s :: Sort) where
  SoProg :: !String -> ScottOut 'SProg
  SoDecl :: !DeclInfo -> ScottOut 'SDecl
  SoExpr :: !String -> ScottOut 'SExpr
  SoVal  :: !String -> !(Maybe Name) -> ScottOut ('SVal m)
  SoArm  :: !String -> !(Maybe Name) -> ScottOut 'SArm

-- | Declaration-level output: data decls and let decls produce
--   full source text; ctor decls produce just their name + arity
--   which the surrounding 'dataDecl' consumes.
data DeclInfo
  = DiCtor !Name !Int  -- ctor name + arity (= number of args)
  | DiData !String     -- the whole data decl's emitted block
  | DiVal  !String     -- a let decl's emitted line

-- | State threaded through 'Scott' methods: ctor-to-parent map
--   (for 'case_' to look up the eliminator name), data-to-
--   ctor-list map (for branch-order in 'case_'), and the
--   load-bearing binder's inferred data type (so 'prog' can
--   pick the right @showX@ companion for 'main = putStrLn').
data Env = Env
  { envCtorParent :: !(Map Name Name)
  , envDataCtors  :: !(Map Name [Name])
  , envRtType     :: !(Maybe Name)
  } deriving Show

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Nothing

-- | The carrier.  Phantom in @a@; state monad in 'Env'.
newtype Scott (a :: Sort -> Type) (s :: Sort) = Scott
  { unScott :: State Env (ScottOut s) }

-- | Render a program down to a Haskell source 'String'.  The
--   emitted module is self-contained: it imports just 'IO' and
--   'putStrLn' (under 'NoImplicitPrelude' to free Ωmegator-
--   declared names) and has a @main = putStrLn (showRt rt)@
--   entry point.  Each emitted data type comes with a
--   hand-derived @showX@ companion so 'main' can print results.
renderScott :: Scott a 'SProg -> String
renderScott s = case evalState (unScott s) emptyEnv of
  SoProg t -> t

-- ----------------------------------------------------------------------
-- Helpers
-- ----------------------------------------------------------------------

-- | Lowercase the first character of a 'Name' — Ωmegator ctors are
--   uppercase, but Scott translates them to value-level functions
--   which Haskell requires to start lowercase.  No collision check
--   today (the @-uppercasing-massage- TODO).
lowerCtor :: Name -> String
lowerCtor n = case T.unpack n of
  []     -> []
  (c:cs) -> toLower c : cs

-- | Count arrows in a type expression text.  Crude — splits on
--   the literal token @ -> @ and subtracts one.  Sufficient for
--   our examples (no nested arrows in argument positions yet).
countArrows :: String -> Int
countArrows s = case words s of
  []  -> 0
  ws  -> length (filter (== "->") ws)

-- | Emit the Haskell source for an entire data declaration:
--   the eliminator newtype, the ctor functions, and a 'show'
--   companion.  Today restricted to nullary ctors only (every
--   branch is @() -> x@; the captured-args case follows when we
--   need it).
emitDataDecl :: Name -> [(Name, Int)] -> String
emitDataDecl dataName ctorInfos =
  let dn       = T.unpack dataName
      elimTy   = dn <> "'"
      ctors    = ctorInfos
      branches = replicate (length ctors) "(() -> x)"
      newtypeLine =
        "newtype " <> elimTy <> " = " <> elimTy <>
        " { un" <> elimTy <> " :: forall x. " <>
        intercalate " -> " (branches <> ["x"]) <> " }"
      ctorFns =
        [ emitCtorFn elimTy i (length ctors) cn
        | (i, (cn, _arity)) <- zip [0 :: Int ..] ctors ]
      showFn = emitShowFn elimTy dn ctors
  in unlines (newtypeLine : "" : ctorFns ++ ["", showFn])

-- | Emit one ctor function: @ci = X' $ \\b1 b2 … bn -> bi ()@.
emitCtorFn :: String -> Int -> Int -> Name -> String
emitCtorFn elimTy idx n cn =
  let cnL = lowerCtor cn
      params = [ "b" <> show i | i <- [0 .. n - 1] ]
      selected = params !! idx
      lambda = "\\" <> unwords params <> " -> " <> selected <> " ()"
  in cnL <> " :: " <> elimTy <> "\n"
     <> cnL <> " = " <> elimTy <> " $ " <> lambda

-- | Emit the show-eliminator for a data type:
--   @showX x = unX' x (\\() -> "C1") (\\() -> "C2") ...@.
emitShowFn :: String -> String -> [(Name, Int)] -> String
emitShowFn elimTy dn ctors =
  let fnName = "show" <> dn
      branches =
        [ "(\\() -> \"" <> T.unpack cn <> "\")"
        | (cn, _arity) <- ctors ]
  in fnName <> " :: " <> elimTy <> " -> String\n"
     <> fnName <> " v = un" <> elimTy <> " v " <> unwords branches

-- ----------------------------------------------------------------------
-- The 'Lang' instance
-- ----------------------------------------------------------------------

instance Lang Scott where

  prog _ann ds = Scott $ do
    declOuts <- mapM unScott ds
    rtTy <- gets envRtType
    let texts =
          [ t
          | d <- declOuts
          , let di = case d of SoDecl x -> x
          , Just t <- [extractDeclText di]
          ]
        showAlias = case rtTy of
          Just dn ->
            let dnS = T.unpack dn
            in "\nshowRt :: " <> dnS <> "' -> String\n"
               <> "showRt = show" <> dnS <> "\n"
          Nothing ->
            "\nshowRt :: String -> String  -- rt type unknown\n"
            <> "showRt = id\n"
        mainBlock =
          "main :: IO ()\n"
          <> "main = putStrLn (showRt rt)\n"
    pure $ SoProg $ unlines
      [ "{-# LANGUAGE NoImplicitPrelude #-}"
      , "{-# LANGUAGE RankNTypes #-}"
      , ""
      , "module Main where"
      , ""
      , "import Prelude (IO, String, putStrLn, ($))"
      , ""
      ] <> unlines texts <> showAlias <> "\n" <> mainBlock

  dataDecl _ann _path name _params _kindExpr ctorScotts = Scott $ do
    ctorOuts <- mapM unScott ctorScotts
    let ctorInfos = [ (cn, a) | SoDecl (DiCtor cn a) <- ctorOuts ]
        ctorNames = map fst ctorInfos
    modify $ \env -> env
      { envDataCtors = Map.insert name ctorNames (envDataCtors env)
      , envCtorParent = Map.union
          (Map.fromList [(cn, name) | cn <- ctorNames])
          (envCtorParent env)
      }
    pure $ SoDecl $ DiData (emitDataDecl name ctorInfos)

  ctorDecl _ann name ty = Scott $ do
    sExpr <- unScott ty
    let tyText = case sExpr of SoExpr t -> t
        arity = countArrows tyText
    pure $ SoDecl (DiCtor name arity)

  -- Type-level methods: emit text fragments so 'ctorDecl' can
  -- compute arity by counting arrows.

  var        _ann n        = Scott $ pure $ SoExpr (T.unpack n)
  tyConRef   _ann n _p     = Scott $ pure $ SoExpr (T.unpack n)
  tyParamRef _ann n _p     = Scott $ pure $ SoExpr (T.unpack n)
  star       _ann _w       = Scott $ pure $ SoExpr "Type"
  arr _ann a b             = Scott $ do
    saA <- unScott a
    saB <- unScott b
    let ta = case saA of SoExpr t -> t
        tb = case saB of SoExpr t -> t
    pure $ SoExpr (ta <> " -> " <> tb)
  app _ann _ap f x         = Scott $ do
    saF <- unScott f
    saX <- unScott x
    let tf = case saF of SoExpr t -> t
        tx = case saX of SoExpr t -> t
    pure $ SoExpr (tf <> " " <> tx)

  -- Value-level methods.

  valDecl _ann _p name body = Scott $ do
    sBody <- unScott body
    let (bodyText, bodyHead) = case sBody of SoVal t h -> (t, h)
    -- Remember the binder's inferred data type so 'prog' can
    -- synthesise the right @showX@ alias.  We just track the
    -- last binder seen (intentional for the demo's
    -- @let rt = …@ shape; multi-binder programs would need a
    -- richer convention).
    modify $ \env -> env { envRtType = bodyHead }
    pure $ SoDecl (DiVal $ T.unpack name <> " = " <> bodyText)

  valVar _ann n _p = Scott $
    pure $ SoVal (T.unpack n) Nothing

  valCtor _ann name _p args = Scott $ do
    argOuts <- mapM unScott args
    parent <- gets (Map.lookup name . envCtorParent)
    let argTexts = [ case ao of SoVal t _ -> t | ao <- argOuts ]
        cnL = lowerCtor name
        text = case argTexts of
          [] -> cnL
          _  -> "(" <> cnL <> " " <> unwords argTexts <> ")"
    pure $ SoVal text parent

  case_ _ann scrut arms = Scott $ do
    sScrut <- unScott scrut
    armOuts <- mapM unScott arms
    let (scrutText, scrutDataTy) = case sScrut of SoVal t h -> (t, h)
        armTexts = [ case ao of SoArm t _ -> t | ao <- armOuts ]
        armDataTys = [ case ao of SoArm _ h -> h | ao <- armOuts ]
    -- Scrut's head already IS the data-type name (valCtor stores
    -- the parent looked up at its emit site).  Fall back to the
    -- first arm's pat-head data type if the scrut is e.g. a
    -- bare variable that didn't carry a head.
    let dataTy = case scrutDataTy of
          Just _  -> scrutDataTy
          Nothing -> case [h | Just h <- armDataTys] of
            (h:_) -> Just h
            _     -> Nothing
    pure $ case dataTy of
      Just dn ->
        let elimFn = "un" <> T.unpack dn <> "'"
            text   = "(" <> elimFn <> " " <> scrutText <> " "
                     <> unwords armTexts <> ")"
        in SoVal text (Just dn)
      Nothing ->
        SoVal ("ERROR_unknown_case_type: " <> scrutText) Nothing

  arm _ann pat body = Scott $ do
    sPat  <- unScott pat
    sBody <- unScott body
    let patHead  = case sPat  of SoVal _ h -> h
        bodyText = case sBody of SoVal t _ -> t
    -- Nullary patterns: branch is @\\() -> body@.
    -- Captured-args case is deferred.
    pure $ SoArm ("(\\() -> " <> bodyText <> ")") patHead

extractDeclText :: DeclInfo -> Maybe String
extractDeclText (DiData t) = Just t
extractDeclText (DiVal  t) = Just t
extractDeclText (DiCtor _ _) = Nothing
