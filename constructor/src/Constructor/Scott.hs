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
--   Three shapes supported:
--
--     1. Nullary ctors (Bool, Iso).  Each branch is @(() -> x)@,
--        each ctor is @\\b0 b1 … -> bi ()@.
--
--     2. Captured-arg ctors (Nat S, etc.).  Each captured arg
--        becomes a branch-lambda parameter and a type position
--        in the branch: @(Nat' -> x)@ for @S@'s captured Nat.
--        Recursive ctors handle themselves because the captured
--        arg's type is the eliminator-newtype @X'@ itself.
--
--     3. Existential ctors (@Pack : ∃m. m -> Foo@).  The
--        existential becomes a rank-2 @forall m.@ inside the
--        branch type: @(forall m. m -> x)@.  Scott's outer
--        result-quantification @forall x.@ and the inner
--        existential-hiding @forall m.@ compose cleanly — the
--        existential is invisible to the eliminator's caller.
--
--   Refining GADTs (Fin) need an index-parameterised @x@
--   ('x :: Index -> Type', branch types refined to @x i@) and
--   are deferred until the carrier grows those.
--
--   The carrier is stateful — a 'State' monad over an 'Env'
--   tracking data-to-ctor associations, so 'case_' can look up
--   the eliminator name from the scrutinee's data type.
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
import Data.List (intercalate, isSuffixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

-- ----------------------------------------------------------------------
-- Per-sort carrier output.
-- ----------------------------------------------------------------------

-- | 'SExpr' values (type-level expressions) carry the emitted
--   text plus the list of currently-in-scope existential type
--   variables (from any 'existsTy' wrappers around them).
--
--   'SVal' values in Dissect mode carry the list of binders the
--   pattern introduces — used by 'arm' to construct the branch
--   lambda's parameters.
data ScottOut (s :: Sort) where
  SoProg :: !String -> ScottOut 'SProg
  SoDecl :: !DeclInfo -> ScottOut 'SDecl
  SoExpr :: !String -> ![Name] -> ScottOut 'SExpr
  SoVal  :: !String -> !(Maybe Name) -> ![Name] -> ScottOut ('SVal m)
  SoArm  :: !String -> !(Maybe Name) -> ScottOut 'SArm

-- | Decl-level emission.  'DiCtor' captures everything 'dataDecl'
--   needs to emit each ctor's Haskell-side definition: its
--   name, the textual types of each captured argument, and the
--   list of existential binders that scope over those captures.
data DeclInfo
  = DiCtor !Name ![String] ![Name]
  | DiData !String
  | DiVal  !String

data Env = Env
  { envCtorParent :: !(Map Name Name)
  , envDataCtors  :: !(Map Name [Name])
  , envRtType     :: !(Maybe Name)
  } deriving Show

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Nothing

newtype Scott (a :: Sort -> Type) (s :: Sort) = Scott
  { unScott :: State Env (ScottOut s) }

renderScott :: Scott a 'SProg -> String
renderScott s = case evalState (unScott s) emptyEnv of
  SoProg t -> t

-- ----------------------------------------------------------------------
-- Helpers
-- ----------------------------------------------------------------------

-- | Lowercase first char (T → t).  Ωmegator ctors are uppercase;
--   Haskell value-level functions are lowercase.
lowerCtor :: Name -> String
lowerCtor n = case T.unpack n of
  []     -> []
  (c:cs) -> toLower c : cs

-- | Split a ctor's annotation text @T1 -> T2 -> ... -> Tk -> R@
--   into ([T1, ..., Tk], R).  Crude — splits on the literal
--   token @ -> @, assumes args don't contain higher-order
--   arrows.  Sufficient for the AxiomsSpec corpus.
splitArrows :: String -> ([String], String)
splitArrows s =
  let parts = go (words s)
  in case reverse parts of
       []     -> ([], "")
       (r:cs) -> (reverse cs, r)
  where
    go [] = []
    go ws = case break (== "->") ws of
      (left, [])       -> [unwords left]
      (left, _ : rest) -> unwords left : go rest

-- | Emit a branch's type signature given its captured-arg types
--   and the existentials that scope over them.
branchTy :: [String] -> [Name] -> String
branchTy [] _ = "(() -> x)"
branchTy caps existentials =
  let prefix = case existentials of
        [] -> ""
        es -> "forall " <> unwords (map T.unpack es) <> ". "
      argsChain = intercalate " -> " (caps <> ["x"])
  in "(" <> prefix <> argsChain <> ")"

-- | Emit the Haskell text for a complete data declaration: the
--   eliminator newtype, each ctor's function definition, and a
--   @showX@ companion that recursively renders the value.
emitDataDecl :: Name -> [(Name, [String], [Name])] -> String
emitDataDecl dataName ctorInfos =
  let dn          = T.unpack dataName
      elimTy      = dn <> "'"
      branches    = [ branchTy caps es | (_, caps, es) <- ctorInfos ]
      newtypeLine = "newtype " <> elimTy <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall x. "
                  <> intercalate " -> " (branches <> ["x"]) <> " }"
      ctorFns =
        [ emitCtorFn elimTy idx (length ctorInfos) cn caps es
        | (idx, (cn, caps, es)) <- zip [0 :: Int ..] ctorInfos ]
      showFn = emitShowFn elimTy dn ctorInfos
  in unlines (newtypeLine : "" : ctorFns ++ ["", showFn])

-- | Emit one ctor function: type signature + value definition.
--   Type signature shape:
--
--     * nullary, no exist : @c :: X'@
--     * captured, no exist: @c :: T1 -> ... -> X'@
--     * existential: @c :: forall e1 e2. T1 -> ... -> X'@
--
--   Value definition shape (for n ctors total, this ctor at index i):
--
--     * nullary: @c = X' $ \\b0 b1 ... bn-1 -> bi ()@
--     * captured: @c a0 a1 ... ak-1 = X' $ \\b0 ... bn-1 -> bi a0 ... ak-1@
emitCtorFn :: String -> Int -> Int -> Name -> [String] -> [Name] -> String
emitCtorFn elimTy idx n cn caps existentials =
  let cnL         = lowerCtor cn
      branchVars  = [ "b" <> show i | i <- [0 .. n - 1] ]
      selected    = branchVars !! idx
      capVars     = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existPrefix = case existentials of
        [] -> ""
        es -> "forall " <> unwords (map T.unpack es) <> ". "
      typeSig = cnL <> " :: " <> existPrefix
              <> intercalate " -> " (caps <> [elimTy])
      lambdaBody = case caps of
        [] -> selected <> " ()"
        _  -> selected <> " " <> unwords capVars
      defHead = cnL <> case caps of
        [] -> ""
        _  -> " " <> unwords capVars
      defLine = defHead <> " = " <> elimTy <> " $ \\"
              <> unwords branchVars <> " -> " <> lambdaBody
  in typeSig <> "\n" <> defLine

-- | Emit the show eliminator.  Each branch renders its ctor's
--   name and recursively shows its captured args.  Args whose
--   type is a known data type (text ends with @'@) get a
--   recursive @showX m@ call; args whose type is existential
--   (a bare type variable) render as @<existential>@ since
--   they have no Show instance reachable from outside the
--   branch.
emitShowFn :: String -> String -> [(Name, [String], [Name])] -> String
emitShowFn elimTy dn ctorInfos =
  let fnName = "show" <> dn
      branches =
        [ emitShowBranch cn caps existentials
        | (cn, caps, existentials) <- ctorInfos ]
  in fnName <> " :: " <> elimTy <> " -> String\n"
     <> fnName <> " v = un" <> elimTy <> " v " <> unwords branches

emitShowBranch :: Name -> [String] -> [Name] -> String
emitShowBranch cn caps existentials =
  let cnStr = T.unpack cn
      capVars = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existSet = map T.unpack existentials
      showOne (capTy, var)
        | capTy `elem` existSet      = "\"<existential>\""
        | "'" `isSuffixOf` capTy     = "show" <> init capTy <> " " <> var
        | otherwise                  = "\"<unrecognised " <> capTy <> ">\""
      pieces = case caps of
        [] -> ["\"" <> cnStr <> "\""]
        _  -> ("\"" <> cnStr <> "\"") : [showOne x | x <- zip caps capVars]
      bodyStr = case caps of
        [] -> head pieces
        _  -> "\"(" <> cnStr <> " \" ++ "
              <> intercalate " ++ \" \" ++ " (tail pieces)
              <> " ++ \")\""
      paramPart = case caps of
        [] -> "()"
        _  -> unwords capVars
  in "(\\" <> paramPart <> " -> " <> bodyStr <> ")"

extractDeclText :: DeclInfo -> Maybe String
extractDeclText (DiData t)     = Just t
extractDeclText (DiVal  t)     = Just t
extractDeclText (DiCtor _ _ _) = Nothing

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
            in "showRt :: " <> dnS <> "' -> String\n"
               <> "showRt = show" <> dnS <> "\n"
          Nothing ->
            "showRt :: String -> String  -- rt type unknown\n"
            <> "showRt s = s\n"
    pure $ SoProg $ unlines
      [ "{-# LANGUAGE NoImplicitPrelude #-}"
      , "{-# LANGUAGE RankNTypes #-}"
      , ""
      , "module Main where"
      , ""
      , "import Prelude (IO, String, putStrLn, ($), (++))"
      , ""
      ] <> unlines texts <> "\n" <> showAlias <> "\n"
        <> "main :: IO ()\n"
        <> "main = putStrLn (showRt rt)\n"

  dataDecl _ann _path name _params _kindExpr ctorScotts = Scott $ do
    ctorOuts <- mapM unScott ctorScotts
    let ctorInfos =
          [ (cn, caps, es)
          | so <- ctorOuts
          , let di = case so of SoDecl x -> x
          , DiCtor cn caps es <- [di]
          ]
        ctorNames = map (\(cn, _, _) -> cn) ctorInfos
    modify $ \env -> env
      { envDataCtors = Map.insert name ctorNames (envDataCtors env)
      , envCtorParent = Map.union
          (Map.fromList [(cn, name) | cn <- ctorNames])
          (envCtorParent env)
      }
    pure $ SoDecl $ DiData (emitDataDecl name ctorInfos)

  ctorDecl _ann name ty = Scott $ do
    sExpr <- unScott ty
    let (tyText, existentials) = case sExpr of SoExpr t es -> (t, es)
        (caps, _result) = splitArrows tyText
    pure $ SoDecl (DiCtor name caps existentials)

  -- ---- Type-level expressions ----------------------------------

  var        _ann n        = Scott $ pure $ SoExpr (T.unpack n) []

  -- Type constructors get a @'@-suffix so they reference the
  -- Scott eliminator newtype rather than (the non-existent)
  -- original Haskell data type.
  tyConRef   _ann n _p     = Scott $ pure $ SoExpr (T.unpack n <> "'") []

  -- Type parameters are plain identifiers (Haskell type variables).
  tyParamRef _ann n _p     = Scott $ pure $ SoExpr (T.unpack n) []

  star       _ann _w       = Scott $ pure $ SoExpr "Type" []

  arr _ann a b             = Scott $ do
    saA <- unScott a
    saB <- unScott b
    let (ta, ea) = case saA of SoExpr t es -> (t, es)
        (tb, eb) = case saB of SoExpr t es -> (t, es)
    pure $ SoExpr (ta <> " -> " <> tb) (ea <> eb)

  app _ann _ap f x         = Scott $ do
    saF <- unScott f
    saX <- unScott x
    let (tf, ef) = case saF of SoExpr t es -> (t, es)
        (tx, ex) = case saX of SoExpr t es -> (t, es)
    pure $ SoExpr (tf <> " " <> tx) (ef <> ex)

  -- Existential type binders: the body's text is unchanged
  -- (Haskell doesn't have surface @∃@; the existential becomes
  -- a 'forall' inside the relevant branch's type, emitted by
  -- 'emitCtorFn').  We just /record/ the binder name in the
  -- propagated existentials list.
  existsTy _ann name _binderPath body = Scott $ do
    sBody <- unScott body
    let (t, es) = case sBody of SoExpr txt xs -> (txt, xs)
    pure $ SoExpr t (name : es)

  -- ---- Value-level expressions ---------------------------------

  valDecl _ann _p name body = Scott $ do
    sBody <- unScott body
    let (bodyText, bodyHead) = case sBody of SoVal t h _ -> (t, h)
    modify $ \env -> env { envRtType = bodyHead }
    pure $ SoDecl (DiVal $ T.unpack name <> " = " <> bodyText)

  -- Variable / pattern binder.  In Dissect mode this is the
  -- introduction site; we report the binder so 'arm' can use
  -- it as a branch-lambda parameter.  In Build mode it's just
  -- a reference (no binders introduced).
  valVar _ann n _p = Scott $
    pure $ SoVal (T.unpack n) Nothing [n]
    -- ^ The [n] is harmless in Build mode (arm only consults
    --   it via the pattern side).

  valCtor _ann name _p args = Scott $ do
    argOuts <- mapM unScott args
    parent <- gets (Map.lookup name . envCtorParent)
    let argTexts = [ case ao of SoVal t _ _ -> t | ao <- argOuts ]
        argBinders = concatMap (\ao -> case ao of SoVal _ _ bs -> bs) argOuts
        cnL = lowerCtor name
        text = case argTexts of
          [] -> cnL
          _  -> "(" <> cnL <> " " <> unwords argTexts <> ")"
    pure $ SoVal text parent argBinders

  case_ _ann scrut arms = Scott $ do
    sScrut <- unScott scrut
    armOuts <- mapM unScott arms
    let (scrutText, scrutDataTy) = case sScrut of SoVal t h _ -> (t, h)
        armTexts = [ case ao of SoArm t _ -> t | ao <- armOuts ]
        armDataTys = [ case ao of SoArm _ h -> h | ao <- armOuts ]
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
        in SoVal text (Just dn) []
      Nothing ->
        SoVal ("ERROR_unknown_case_type: " <> scrutText) Nothing []

  arm _ann pat body = Scott $ do
    sPat  <- unScott pat
    sBody <- unScott body
    let patHead    = case sPat  of SoVal _ h _  -> h
        patBinders = case sPat  of SoVal _ _ bs -> bs
        bodyText   = case sBody of SoVal t _ _  -> t
        paramPart = case patBinders of
          [] -> "()"
          bs -> unwords (map T.unpack bs)
    pure $ SoArm
      ("(\\" <> paramPart <> " -> " <> bodyText <> ")")
      patHead
