{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

-- | A Scott-encoding Haskell-source carrier of the 'Lang' algebra.
--
--   Four ctor shapes supported:
--
--     1. Nullary, non-parametric (Bool, Iso): branch type @(() -> x)@.
--     2. Captured-arg, non-parametric (Nat S): branch type @(T -> x)@.
--     3. Existential (Pack ∃m.): branch type @(forall m. m -> x)@.
--     4. Refining GADT (Fin, Expr): the eliminator's @x@ is
--        index-parameterised (@forall (x :: Index -> Type)@), and
--        each branch's result type is @x@ at the ctor's refined
--        index — @x Z'@ for FZ, @forall n. Fin' n -> x (S' n)@ for
--        FS.  The Const-trick is used in @showX@ to extract a
--        String from an indexed result.
--
--   The encoding switches between non-parametric and parametric
--   based on whether the data declaration's parameter list is
--   empty.  Both shapes coexist in the same module — Bool can
--   live alongside Fin, each with its own elim discipline.
module Constructor.Scott
  ( Scott
  , renderScott
  ) where

import Constructor.Path (Path)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Control.Monad.State (State, evalState, get, gets, modify)
import Data.Char (toLower)
import Data.Kind (Type)
import Data.List (intercalate, isSuffixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T

data ScottOut (s :: Sort) where
  SoProg :: !String -> ScottOut 'SProg
  SoDecl :: !DeclInfo -> ScottOut 'SDecl
  SoExpr :: !String -> ![Name] -> ScottOut 'SExpr
  SoVal  :: !String -> !(Maybe Name) -> ![Name] -> ScottOut ('SVal m)
  SoArm  :: !String -> !(Maybe Name) -> ScottOut 'SArm

data DeclInfo
  = DiCtor !Name ![String] ![String] ![Name]
    -- ^ ctor name, captured-arg types, result-index args, existentials
  | DiData !String
  | DiVal  !String

data Env = Env
  { envCtorParent :: !(Map Name Name)
  , envDataCtors  :: !(Map Name [Name])
  , envDataParams :: !(Map Name [(Name, String)])
    -- ^ data name → list of (param name, param kind text)
  , envRtType     :: !(Maybe Name)
  } deriving Show

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Map.empty Nothing

newtype Scott (a :: Sort -> Type) (s :: Sort) = Scott
  { unScott :: State Env (ScottOut s) }

renderScott :: Scott a 'SProg -> String
renderScott s = case evalState (unScott s) emptyEnv of
  SoProg t -> t

-- ----------------------------------------------------------------------
-- Helpers
-- ----------------------------------------------------------------------

lowerCtor :: Name -> String
lowerCtor n = case T.unpack n of
  []     -> []
  (c:cs) -> toLower c : cs

-- | Split a ctor's annotation text into ([captured arg types], result).
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

-- | Split a string on top-level whitespace, respecting parentheses.
--   E.g., "Fin' (S' n)" → ["Fin'", "(S' n)"].
splitTopLevel :: String -> [String]
splitTopLevel s = reverse (map reverse (go s 0 [] []))
  where
    go [] _ cur acc
      | null cur  = acc
      | otherwise = cur : acc
    go (c:cs) 0 cur acc
      | c == ' '  = if null cur then go cs 0 [] acc else go cs 0 [] (cur : acc)
      | c == '('  = go cs 1 (c : cur) acc
      | otherwise = go cs 0 (c : cur) acc
    go (c:cs) d cur acc
      | c == '('  = go cs (d + 1) (c : cur) acc
      | c == ')'  = go cs (d - 1) (c : cur) acc
      | otherwise = go cs d (c : cur) acc

extractDeclText :: DeclInfo -> Maybe String
extractDeclText (DiData t)         = Just t
extractDeclText (DiVal  t)         = Just t
extractDeclText (DiCtor _ _ _ _)   = Nothing

-- ----------------------------------------------------------------------
-- Non-parametric emission (Bool, Iso, Nat-style)
-- ----------------------------------------------------------------------

branchTyNonParam :: [String] -> [Name] -> String
branchTyNonParam [] _ = "(() -> x)"
branchTyNonParam caps existentials =
  let prefix = case existentials of
        [] -> ""
        es -> "forall " <> unwords (map T.unpack es) <> ". "
  in "(" <> prefix <> intercalate " -> " (caps <> ["x"]) <> ")"

emitNonParametric
  :: Name -> [(Name, [String], [String], [Name])] -> String
emitNonParametric dataName ctorInfos =
  let dn          = T.unpack dataName
      elimTy      = dn <> "'"
      branches    =
        [ branchTyNonParam caps es | (_, caps, _, es) <- ctorInfos ]
      newtypeLine = "newtype " <> elimTy <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall x. "
                  <> intercalate " -> " (branches <> ["x"]) <> " }"
      ctorFns =
        [ emitCtorFnNonParam elimTy idx (length ctorInfos) cn caps es
        | (idx, (cn, caps, _, es)) <- zip [0 :: Int ..] ctorInfos ]
      showFn = emitShowFnNonParam elimTy dn ctorInfos
  in unlines (newtypeLine : "" : ctorFns ++ ["", showFn])

emitCtorFnNonParam
  :: String -> Int -> Int -> Name -> [String] -> [Name] -> String
emitCtorFnNonParam elimTy idx n cn caps existentials =
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

emitShowFnNonParam
  :: String -> String -> [(Name, [String], [String], [Name])] -> String
emitShowFnNonParam elimTy dn ctorInfos =
  let fnName = "show" <> dn
      branches =
        [ emitShowBranchNonParam cn caps es
        | (cn, caps, _, es) <- ctorInfos ]
  in fnName <> " :: " <> elimTy <> " -> String\n"
     <> fnName <> " v = un" <> elimTy <> " v " <> unwords branches

emitShowBranchNonParam :: Name -> [String] -> [Name] -> String
emitShowBranchNonParam cn caps existentials =
  let cnStr = T.unpack cn
      capVars = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existSet = map T.unpack existentials
      showOne (capTy, var)
        | capTy `elem` existSet      = "\"<existential>\""
        | "'" `isSuffixOf` capTy     = "show" <> init capTy <> " " <> var
        | otherwise                  = "\"<unrecognised " <> capTy <> ">\""
      bodyStr = case caps of
        [] -> "\"" <> cnStr <> "\""
        _  -> "\"(" <> cnStr <> " \" ++ "
              <> intercalate " ++ \" \" ++ "
                   [showOne x | x <- zip caps capVars]
              <> " ++ \")\""
      paramPart = case caps of
        [] -> "()"
        _  -> unwords capVars
  in "(\\" <> paramPart <> " -> " <> bodyStr <> ")"

-- ----------------------------------------------------------------------
-- Non-refining parametric (Maybe, regular Tree, non-regular Nest)
-- — regular Scott with the type variables threaded through the newtype.
-- No HKT 'forall (x :: K -> Type)' needed; 'x' is just 'Type'.
-- ----------------------------------------------------------------------

emitNonRefining
  :: Name -> [(Name, String)]
  -> [(Name, [String], [String], [Name])] -> String
emitNonRefining dataName params ctorInfos =
  let dn        = T.unpack dataName
      elimTy    = dn <> "'"
      paramSig  = unwords
        [ "(" <> T.unpack pn <> " :: " <> pk <> ")" | (pn, pk) <- params ]
      paramRefs = unwords [ T.unpack pn | (pn, _) <- params ]
      branches  =
        [ branchTyNonParam caps es | (_, caps, _, es) <- ctorInfos ]
      newtypeLine = "newtype " <> elimTy <> " " <> paramSig
                  <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall x. "
                  <> intercalate " -> " (branches <> ["x"]) <> " }"
      ctorFns =
        [ emitCtorFnNonRefining elimTy paramRefs idx (length ctorInfos)
                                  cn caps es
        | (idx, (cn, caps, _, es)) <- zip [0 :: Int ..] ctorInfos ]
      showFn = emitShowFnNonRefining dn elimTy paramRefs ctorInfos
  in unlines (newtypeLine : "" : ctorFns ++ ["", showFn])

emitCtorFnNonRefining
  :: String -> String -> Int -> Int -> Name -> [String] -> [Name] -> String
emitCtorFnNonRefining elimTy paramRefs idx n cn caps existentials =
  let cnL         = lowerCtor cn
      branchVars  = [ "b" <> show i | i <- [0 .. n - 1] ]
      selected    = branchVars !! idx
      capVars     = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existPrefix = case existentials of
        [] -> ""
        es -> "forall " <> unwords (map T.unpack es) <> ". "
      resultTy = elimTy <> " " <> paramRefs
      typeSig = cnL <> " :: " <> existPrefix
              <> intercalate " -> " (caps <> [resultTy])
      lambdaBody = case caps of
        [] -> selected <> " ()"
        _  -> selected <> " " <> unwords capVars
      defHead = cnL <> case caps of
        [] -> ""
        _  -> " " <> unwords capVars
      defLine = defHead <> " = " <> elimTy <> " $ \\"
              <> unwords branchVars <> " -> " <> lambdaBody
  in typeSig <> "\n" <> defLine

emitShowFnNonRefining
  :: String -> String -> String
  -> [(Name, [String], [String], [Name])] -> String
emitShowFnNonRefining dn elimTy paramRefs ctorInfos =
  let fnName   = "show" <> dn
      branches =
        [ emitShowBranchNonParam cn caps es
        | (cn, caps, _, es) <- ctorInfos ]
  in fnName <> " :: forall " <> paramRefs <> ". " <> elimTy <> " "
     <> paramRefs <> " -> String\n"
     <> fnName <> " v = un" <> elimTy <> " v " <> unwords branches

-- ----------------------------------------------------------------------
-- Parametric emission (Fin, Expr — indexed eliminators)
-- ----------------------------------------------------------------------

branchTyParam :: [String] -> [String] -> [Name] -> String
branchTyParam caps resultArgs existentials =
  let prefix = case existentials of
        [] -> ""
        es -> "forall " <> unwords (map T.unpack es) <> ". "
      xApplied = case resultArgs of
        [] -> "x"
        rs -> "x " <> unwords rs
      -- Uniform thunking on nullary so the elim branch types match
      -- what 'arm' emits.
      chain = case caps of
        [] -> "() -> " <> xApplied
        _  -> intercalate " -> " (caps <> [xApplied])
  in "(" <> prefix <> chain <> ")"

emitParametric
  :: Name -> [(Name, String)]
  -> [(Name, [String], [String], [Name])] -> String
emitParametric dataName params ctorInfos =
  let dn       = T.unpack dataName
      elimTy   = dn <> "'"
      paramSig = unwords
        [ "(" <> T.unpack pn <> " :: " <> pk <> ")" | (pn, pk) <- params ]
      paramRefs = unwords [ T.unpack pn | (pn, _) <- params ]
      xKindChain = concat [ pk <> " -> " | (_, pk) <- params ] <> "Type"
      branches =
        [ branchTyParam caps res es
        | (_, caps, res, es) <- ctorInfos ]
      xApplied = "x " <> paramRefs
      newtypeLine = "newtype " <> elimTy <> " " <> paramSig
                  <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall (x :: "
                  <> xKindChain <> "). "
                  <> intercalate " -> " (branches <> [xApplied])
                  <> " }"
      ctorFns =
        [ emitCtorFnParam dn elimTy idx (length ctorInfos) cn caps res es
        | (idx, (cn, caps, res, es)) <- zip [0 :: Int ..] ctorInfos ]
      showFn = emitShowFnParam dn elimTy params ctorInfos
  in unlines (newtypeLine : "" : ctorFns ++ ["", showFn])

emitCtorFnParam
  :: String -> String -> Int -> Int -> Name -> [String] -> [String]
  -> [Name] -> String
emitCtorFnParam dn elimTy idx n cn caps resultArgs existentials =
  let cnL         = lowerCtor cn
      branchVars  = [ "b" <> show i | i <- [0 .. n - 1] ]
      selected    = branchVars !! idx
      capVars     = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existPrefix = case existentials of
        [] -> ""
        es -> "forall " <> unwords (map T.unpack es) <> ". "
      resultTy = case resultArgs of
        [] -> elimTy
        rs -> elimTy <> " " <> unwords rs
      typeSig = cnL <> " :: " <> existPrefix
              <> intercalate " -> " (caps <> [resultTy])
      -- Match the thunked nullary branch type: invoke with @()@.
      lambdaBody = case caps of
        [] -> selected <> " ()"
        _  -> selected <> " " <> unwords capVars
      defHead = cnL <> case caps of
        [] -> ""
        _  -> " " <> unwords capVars
      defLine = defHead <> " = " <> elimTy <> " $ \\"
              <> unwords branchVars <> " -> " <> lambdaBody
      _suppress = (idx, n, dn)
  in typeSig <> "\n" <> defLine

-- | Show for parametric data uses the Const trick: pick @x = Const
--   String@ so each branch produces a Const-wrapped String at its
--   refined index, then 'getConst' to extract.
emitShowFnParam
  :: String -> String -> [(Name, String)]
  -> [(Name, [String], [String], [Name])] -> String
emitShowFnParam dn elimTy params ctorInfos =
  let fnName     = "show" <> dn
      paramRefs  = unwords [ T.unpack pn | (pn, _) <- params ]
      paramFor   = unwords [ T.unpack pn | (pn, _) <- params ]
      branches   =
        [ emitShowBranchParam cn caps es
        | (cn, caps, _, es) <- ctorInfos ]
  in fnName <> " :: forall " <> paramFor <> ". " <> elimTy <> " "
     <> paramRefs <> " -> String\n"
     <> fnName <> " v = getConst (un" <> elimTy
     <> " v " <> unwords branches <> ")"

emitShowBranchParam :: Name -> [String] -> [Name] -> String
emitShowBranchParam cn caps existentials =
  let cnStr = T.unpack cn
      capVars = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existSet = map T.unpack existentials
      showOne (capTy, var)
        | capTy `elem` existSet  = "\"<existential>\""
        | "'" `isSuffixOf` capTy = "show" <> init capTy <> " " <> var
        | otherwise              = "\"<unrecognised " <> capTy <> ">\""
      bodyStr = case caps of
        [] -> "Const \"" <> cnStr <> "\""
        _  -> "Const (\"(" <> cnStr <> " \" ++ "
              <> intercalate " ++ \" \" ++ "
                   [showOne x | x <- zip caps capVars]
              <> " ++ \")\")"
      paramPart = case caps of
        [] -> "()"
        _  -> unwords capVars
  in "(\\" <> paramPart <> " -> " <> bodyStr <> ")"

-- ----------------------------------------------------------------------
-- The 'Lang' instance
-- ----------------------------------------------------------------------

instance Lang Scott where

  prog _ann ds = Scott $ do
    declOuts <- mapM unScott ds
    env <- get
    let rtTy      = envRtType env
        dataParams = envDataParams env
        texts =
          [ t
          | d <- declOuts
          , let di = case d of SoDecl x -> x
          , Just t <- [extractDeclText di]
          ]
        showAlias = case rtTy of
          Just dn ->
            let dnS = T.unpack dn
                params = Map.findWithDefault [] dn dataParams
            in case params of
                 [] ->
                   "showRt :: " <> dnS <> "' -> String\n"
                   <> "showRt = show" <> dnS <> "\n"
                 _  ->
                   let pvs = unwords [ T.unpack pn | (pn, _) <- params ]
                   in "showRt :: forall " <> pvs <> ". " <> dnS <> "' "
                      <> pvs <> " -> String\n"
                      <> "showRt = show" <> dnS <> "\n"
          Nothing ->
            "showRt :: String -> String  -- rt type unknown\n"
            <> "showRt s = s\n"
        -- The parametric-vs-non-parametric showRt signature
        -- differs if rt's type is parametric — patch via type
        -- ascription helpers if needed.  For arity-1 cases we
        -- assume the caller writes 'rt :: Fin' (S' Z')' or
        -- relies on Haskell inference.
    pure $ SoProg $ unlines
      [ "{-# LANGUAGE NoImplicitPrelude #-}"
      , "{-# LANGUAGE DataKinds #-}"
      , "{-# LANGUAGE KindSignatures #-}"
      , "{-# LANGUAGE RankNTypes #-}"
      , "{-# LANGUAGE ScopedTypeVariables #-}"
      , "{-# OPTIONS_GHC -Wno-name-shadowing #-}"
      , ""
      , "module Main where"
      , ""
      , "import Prelude (IO, String, putStrLn, ($), (++))"
      , "import Data.Functor.Const (Const (..), getConst)"
      , "import Data.Kind (Type)"
      , ""
      ] <> unlines texts <> "\n" <> showAlias <> "\n"
        <> "main :: IO ()\n"
        <> "main = putStrLn (showRt rt)\n"

  dataDecl _ann _path name params _kindExpr ctorScotts = Scott $ do
    -- Elaborate params' kind expressions to text fragments.
    paramKindTexts <- mapM elabKind params
    ctorOuts <- mapM unScott ctorScotts
    let paramList =
          [ (pn, pk) | (pn, pk) <- paramKindTexts ]
        ctorInfos =
          [ (cn, caps, res, es)
          | so <- ctorOuts
          , let di = case so of SoDecl x -> x
          , DiCtor cn caps res es <- [di]
          ]
        ctorNames = [ cn | (cn, _, _, _) <- ctorInfos ]
    modify $ \env -> env
      { envDataCtors = Map.insert name ctorNames (envDataCtors env)
      , envCtorParent = Map.union
          (Map.fromList [(cn, name) | cn <- ctorNames])
          (envCtorParent env)
      , envDataParams = Map.insert name paramList (envDataParams env)
      }
    let paramNames = [ T.unpack pn | (pn, _) <- paramList ]
        refining =
          any (\(_, _, resArgs, _) -> resArgs /= paramNames) ctorInfos
        emitted = case paramList of
          []                  -> emitNonParametric name ctorInfos
          _ | not refining    -> emitNonRefining name paramList ctorInfos
            | otherwise       -> emitParametric name paramList ctorInfos
    pure $ SoDecl $ DiData emitted
    where
      elabKind :: (Name, Maybe (Scott a 'SExpr)) -> State Env (Name, String)
      elabKind (pn, Nothing)     = pure (pn, "Type")
      elabKind (pn, Just kindS)  = do
        sExpr <- unScott kindS
        let t = case sExpr of SoExpr txt _ -> txt
        pure (pn, t)

  ctorDecl _ann name ty = Scott $ do
    sExpr <- unScott ty
    let (tyText, existentials) = case sExpr of SoExpr t es -> (t, es)
        (caps, resultText) = splitArrows tyText
        -- Result is "Bool'" or "Fin' Z'" or "Fin' (S' n)".  Tokenise
        -- top-level, drop the parent head, keep the index args.
        resultArgs = case splitTopLevel resultText of
          []     -> []
          (_:rs) -> rs
    pure $ SoDecl (DiCtor name caps resultArgs existentials)

  -- ---- Type-level expressions ----------------------------------

  var        _ann n        = Scott $ pure $ SoExpr (T.unpack n) []
  tyConRef   _ann n _p     = Scott $ pure $ SoExpr (T.unpack n <> "'") []
  tyParamRef _ann n _p     = Scott $ pure $ SoExpr (T.unpack n) []
  star       _ann _w       = Scott $ pure $ SoExpr "Type" []

  arr _ann a b = Scott $ do
    saA <- unScott a
    saB <- unScott b
    let (ta, ea) = case saA of SoExpr t es -> (t, es)
        (tb, eb) = case saB of SoExpr t es -> (t, es)
    pure $ SoExpr (ta <> " -> " <> tb) (ea <> eb)

  app _ann _ap f x = Scott $ do
    saF <- unScott f
    saX <- unScott x
    let (tf, ef) = case saF of SoExpr t es -> (t, es)
        (tx, ex) = case saX of SoExpr t es -> (t, es)
        -- Parenthesise compound args so splitTopLevel can recover
        -- the spine downstream.
        txP = if ' ' `elem` tx then "(" <> tx <> ")" else tx
    pure $ SoExpr (tf <> " " <> txP) (ef <> ex)

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

  valVar _ann n _p = Scott $
    pure $ SoVal (T.unpack n) Nothing [n]

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
        -- Uniformly thunk nullary branches with @\\() ->@.  Both
        -- non-parametric and parametric branches use this shape,
        -- so the encoding stays consistent across regimes.
        branchText = case patBinders of
          [] -> "(\\() -> " <> bodyText <> ")"
          bs -> "(\\" <> unwords (map T.unpack bs) <> " -> "
                <> bodyText <> ")"
    pure $ SoArm branchText patHead
