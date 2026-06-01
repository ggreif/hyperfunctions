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
  = DiCtor !Name ![String] ![String] ![Name] ![Name]
    -- ^ ctor name, captured-arg types, result-index args,
    --   explicit existentials (from @∃m.@), tyParamRefs seen
    --   in this ctor's annotation.  The seenRefs list is
    --   consumed only by refining-GADT emission to forall'-
    --   bind the parent-parameter references at each ctor
    --   site; non-refining emit ignores it.
  | DiData !String
  | DiVal  !String

data Env = Env
  { envCtorParent :: !(Map Name Name)
  , envDataCtors  :: !(Map Name [Name])
  , envDataParams :: !(Map Name [(Name, String)])
    -- ^ data name → list of (param name, param kind text)
  , envRtType     :: !(Maybe Name)
  , envInKind     :: !Bool
    -- ^ 'True' while elaborating a parameter's kind annotation
    --   (the @K@ in @(n : K)@).  In that context 'tyConRef'
    --   emits the /Haskell data/ name (no tick) so the result
    --   is DataKinds-promotable; outside, it emits the Scott
    --   newtype name (with tick) for runtime types.
  , envCurrentParams :: ![Name]
    -- ^ Names of the parametric data type currently being
    --   processed.  References to these inside a ctor's
    --   annotation become per-ctor foralls (the parent
    --   param flows in as a universal at the ctor's type).
  , envTyParamSeen :: ![Name]
    -- ^ tyParamRefs encountered during the current ctor's
    --   annotation elaboration.  Intersected with
    --   'envCurrentParams' to determine which parent params
    --   should be forall'd at the ctor level.
  } deriving Show

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Map.empty Nothing False [] []

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
extractDeclText DiCtor {}          = Nothing

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
  :: Name -> [(Name, [String], [String], [Name], [Name])] -> String
emitNonParametric dataName ctorInfos =
  let dn          = T.unpack dataName
      elimTy      = dn <> "'"
      -- Regular Haskell data with DataKinds-promotable ctors —
      -- emitted only when no ctor has existential binders (those
      -- would require ExistentialQuantification + a GADT-style
      -- emission, which we skip for now; data types with
      -- existentials aren't useful as kinds anyway).
      hasExistentials = any (\(_, _, _, es, _) -> not (null es)) ctorInfos
      regCtor (cn, caps, _, _, _) =
        T.unpack cn <> case caps of
          [] -> ""
          _  -> " " <> unwords (map stripTicks caps)
      regDataLine
        | hasExistentials = ""
        | otherwise =
            "data " <> dn <> " = "
            <> intercalate " | " (map regCtor ctorInfos)
            <> " deriving Show\n\n"
      branches    =
        [ branchTyNonParam caps es | (_, caps, _, es, _) <- ctorInfos ]
      newtypeLine = "newtype " <> elimTy <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall x. "
                  <> intercalate " -> " (branches <> ["x"]) <> " }"
      ctorFns =
        [ emitCtorFnNonParam elimTy idx (length ctorInfos) cn caps es
        | (idx, (cn, caps, _, es, _)) <- zip [0 :: Int ..] ctorInfos ]
      showFn = emitShowFnNonParam elimTy dn ctorInfos
  in regDataLine <> unlines (newtypeLine : "" : ctorFns ++ ["", showFn])

-- | Strip a trailing @'@ from each whitespace-separated token —
--   used to convert Scott type-text back to its Haskell-data
--   form when emitting the regular @data X = …@ that pairs with
--   the Scott newtype.
stripTicks :: String -> String
stripTicks = unwords . map stripOne . words
  where
    stripOne w = case reverse w of
      '\'':rest -> reverse rest
      _         -> w

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
  :: String -> String -> [(Name, [String], [String], [Name], [Name])] -> String
emitShowFnNonParam elimTy dn ctorInfos =
  let fnName = "show" <> dn
      branches =
        [ emitShowBranchNonParam cn caps es
        | (cn, caps, _, es, _) <- ctorInfos ]
  in fnName <> " :: " <> elimTy <> " -> String\n"
     <> fnName <> " v = un" <> elimTy <> " v " <> unwords branches

emitShowBranchNonParam :: Name -> [String] -> [Name] -> String
emitShowBranchNonParam cn caps existentials =
  let cnStr = T.unpack cn
      capVars = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existSet = map T.unpack existentials
      showOne (capTy, var) = case words capTy of
        (t1 : _) | "'" `isSuffixOf` t1 ->
          -- Scott-typed arg (e.g. "Nat'" or "Fin' n"): recurse
          -- via 'showX' where X is the unticked name.
          "show" <> init t1 <> " " <> var
        _ | capTy `elem` existSet ->
            "\"<existential>\""
        _ -> "\"<unrecognised " <> capTy <> ">\""
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
  -> [(Name, [String], [String], [Name], [Name])] -> String
emitNonRefining dataName params ctorInfos =
  let dn        = T.unpack dataName
      elimTy    = dn <> "'"
      paramSig  = unwords
        [ "(" <> T.unpack pn <> " :: " <> pk <> ")" | (pn, pk) <- params ]
      paramRefs = unwords [ T.unpack pn | (pn, _) <- params ]
      branches  =
        [ branchTyNonParam caps es | (_, caps, _, es, _) <- ctorInfos ]
      newtypeLine = "newtype " <> elimTy <> " " <> paramSig
                  <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall x. "
                  <> intercalate " -> " (branches <> ["x"]) <> " }"
      ctorFns =
        [ emitCtorFnNonRefining elimTy paramRefs idx (length ctorInfos)
                                  cn caps es
        | (idx, (cn, caps, _, es, _)) <- zip [0 :: Int ..] ctorInfos ]
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
  -> [(Name, [String], [String], [Name], [Name])] -> String
emitShowFnNonRefining dn elimTy paramRefs ctorInfos =
  let fnName   = "show" <> dn
      branches =
        [ emitShowBranchNonParam cn caps es
        | (cn, caps, _, es, _) <- ctorInfos ]
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
  -> [(Name, [String], [String], [Name], [Name])] -> String
emitParametric dataName params ctorInfos =
  let dn       = T.unpack dataName
      elimTy   = dn <> "'"
      paramSig = unwords
        [ "(" <> T.unpack pn <> " :: " <> pk <> ")" | (pn, pk) <- params ]
      paramRefs = unwords [ T.unpack pn | (pn, _) <- params ]
      xKindChain = concat [ pk <> " -> " | (_, pk) <- params ] <> "Type"
      -- Per-type show-wrapper: a newtype-of-String with the same kind
      -- shape as the eliminator's @x@.  Used by 'showD' (below) in
      -- place of 'Const' — 'Const' only has one phantom slot, so it
      -- works for single-param indexed types (Fin n) but fails for
      -- multi-param indexed types (List a n, Expr a, …).  This
      -- wrapper has exactly the right arity.
      showWrapTy = "Show" <> dn
      showWrapLine = "newtype " <> showWrapTy <> " " <> paramSig
                  <> " = " <> showWrapTy
                  <> " { un" <> showWrapTy <> " :: String }"
      -- For refining-GADT branches, parent params referenced by
      -- the ctor become per-use foralls in the branch's type
      -- (FS's @n@ is fresh at each elim site).  Combine explicit
      -- existentials with parent-param refs here, then thread to
      -- the branch type / ctor fn / show fn emitters.
      enrichedInfos =
        [ (cn, caps, res, nub (es <> seen))
        | (cn, caps, res, es, seen) <- ctorInfos ]
      branches =
        [ branchTyParam caps res es
        | (_, caps, res, es) <- enrichedInfos ]
      xApplied = "x " <> paramRefs
      newtypeLine = "newtype " <> elimTy <> " " <> paramSig
                  <> " = " <> elimTy
                  <> " { un" <> elimTy <> " :: forall (x :: "
                  <> xKindChain <> "). "
                  <> intercalate " -> " (branches <> [xApplied])
                  <> " }"
      ctorFns =
        [ emitCtorFnParam dn elimTy idx (length enrichedInfos) cn caps res es
        | (idx, (cn, caps, res, es)) <- zip [0 :: Int ..] enrichedInfos ]
      showFn = emitShowFnParam dn elimTy showWrapTy params enrichedInfos
  in unlines (newtypeLine : "" : showWrapLine : "" : ctorFns ++ ["", showFn])
  where
    nub :: Eq a => [a] -> [a]
    nub []     = []
    nub (x:xs) = x : nub (filter (/= x) xs)

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

-- | Show for parametric data uses a per-type show-wrapper (passed
--   in as @showWrapTy@): pick @x = Show<DN>@ so each branch
--   produces a wrapped String at its refined index, then
--   'un<showWrapTy>' to extract.  Replaces an earlier @Const String@
--   approach that only worked for single-param indexed types.
emitShowFnParam
  :: String -> String -> String -> [(Name, String)]
  -> [(Name, [String], [String], [Name])] -> String
emitShowFnParam dn elimTy showWrapTy params ctorInfos =
  let fnName     = "show" <> dn
      paramRefs  = unwords [ T.unpack pn | (pn, _) <- params ]
      paramFor   = unwords [ T.unpack pn | (pn, _) <- params ]
      branches   =
        [ emitShowBranchParam showWrapTy cn caps es
        | (cn, caps, _, es) <- ctorInfos ]
  in fnName <> " :: forall " <> paramFor <> ". " <> elimTy <> " "
     <> paramRefs <> " -> String\n"
     <> fnName <> " v = un" <> showWrapTy <> " (un" <> elimTy
     <> " v " <> unwords branches <> ")"

emitShowBranchParam :: String -> Name -> [String] -> [Name] -> String
emitShowBranchParam showWrapTy cn caps existentials =
  let cnStr = T.unpack cn
      capVars = [ "a" <> show i | i <- [0 .. length caps - 1] ]
      existSet = map T.unpack existentials
      showOne (capTy, var) = case words capTy of
        (t1 : _) | "'" `isSuffixOf` t1 ->
          "show" <> init t1 <> " " <> var
        _ | capTy `elem` existSet ->
            "\"<existential>\""
        _ -> "\"<unrecognised " <> capTy <> ">\""
      bodyStr = case caps of
        [] -> showWrapTy <> " \"" <> cnStr <> "\""
        _  -> showWrapTy <> " (\"(" <> cnStr <> " \" ++ "
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
      , "import Prelude (IO, String, putStrLn, ($), (++), Show)"
      , "import Data.Functor.Const (Const (..), getConst)"
      , "import Data.Kind (Type)"
      , ""
      ] <> unlines texts <> "\n" <> showAlias <> "\n"
        <> "main :: IO ()\n"
        <> "main = putStrLn (showRt rt)\n"

  dataDecl _ann _path name params _kindExpr ctorScotts = Scott $ do
    -- Elaborate params' kind expressions to text fragments.
    paramKindTexts <- mapM elabKind params
    -- Make the parent's param names available to each ctorDecl
    -- so it can detect tyParamRefs to them and add them to its
    -- existentials list (parent params used in ctor signatures
    -- flow in as per-ctor foralls in the Scott emit).
    let paramNames = [ pn | (pn, _) <- params ]
    savedParams <- gets envCurrentParams
    modify $ \e -> e { envCurrentParams = paramNames }
    ctorOuts <- mapM unScott ctorScotts
    modify $ \e -> e { envCurrentParams = savedParams }
    let paramList =
          [ (pn, pk) | (pn, pk) <- paramKindTexts ]
        ctorInfos =
          [ (cn, caps, res, es, seen)
          | so <- ctorOuts
          , let di = case so of SoDecl x -> x
          , DiCtor cn caps res es seen <- [di]
          ]
        ctorNames = [ cn | (cn, _, _, _, _) <- ctorInfos ]
    modify $ \env -> env
      { envDataCtors = Map.insert name ctorNames (envDataCtors env)
      , envCtorParent = Map.union
          (Map.fromList [(cn, name) | cn <- ctorNames])
          (envCtorParent env)
      , envDataParams = Map.insert name paramList (envDataParams env)
      }
    let paramNamesStr = [ T.unpack pn | (pn, _) <- paramList ]
        refining =
          any (\(_, _, resArgs, _, _) -> resArgs /= paramNamesStr) ctorInfos
        emitted = case paramList of
          []                  -> emitNonParametric name ctorInfos
          _ | not refining    -> emitNonRefining name paramList ctorInfos
            | otherwise       -> emitParametric name paramList ctorInfos
    pure $ SoDecl $ DiData emitted
    where
      elabKind :: (Name, Maybe (Scott a 'SExpr)) -> State Env (Name, String)
      elabKind (pn, Nothing)     = pure (pn, "Type")
      elabKind (pn, Just kindS)  = do
        modify $ \e -> e { envInKind = True }
        sExpr <- unScott kindS
        modify $ \e -> e { envInKind = False }
        let t = case sExpr of SoExpr txt _ -> txt
        pure (pn, t)

  ctorDecl _ann name ty = Scott $ do
    -- Reset tyParamRef-seen list for THIS ctor; the result is
    -- stored on the carrier and consumed selectively by
    -- emitParametric (refining) only.
    modify $ \e -> e { envTyParamSeen = [] }
    sExpr <- unScott ty
    seen   <- gets envTyParamSeen
    params <- gets envCurrentParams
    let (tyText, explicitEx) = case sExpr of SoExpr t es -> (t, es)
        (caps, resultText)   = splitArrows tyText
        resultArgs = case splitTopLevel resultText of
          []     -> []
          (_:rs) -> rs
        seenInParents = nubL (filter (`elem` params) seen)
    pure $ SoDecl (DiCtor name caps resultArgs explicitEx seenInParents)
    where
      nubL :: Eq a => [a] -> [a]
      nubL []     = []
      nubL (x:xs) = x : nubL (filter (/= x) xs)

  -- ---- Type-level expressions ----------------------------------

  var        _ann n        = Scott $ pure $ SoExpr (T.unpack n) []
  tyConRef _ann n _p = Scott $ do
    isCtor <- gets (Map.member n . envCtorParent)
    inKind <- gets envInKind
    let nStr = T.unpack n
        -- Ctors emit unticked (DataKinds-promoted, e.g. 'Z' for
        -- the Z ctor of Nat).  Data types emit unticked in kind
        -- context (the @K@ in @(n :: K)@) and ticked in type
        -- context (the captured-arg-type / result-spine head
        -- positions, where they refer to the Scott newtype).
        tick = not isCtor && not inKind
    pure $ SoExpr (nStr <> if tick then "'" else "") []
  tyParamRef _ann n _p = Scott $ do
    modify $ \e -> e { envTyParamSeen = n : envTyParamSeen e }
    pure $ SoExpr (T.unpack n) []
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

  -- Lambda: emit a parenthesised Haskell lambda directly.  The
  -- result's data-type slot inherits from the body — a lambda's
  -- "result data type" IS its body's data type (under any
  -- argument), so this propagates the case_/envRtType signal up
  -- through nested lambdas correctly.
  valLam _ann name _bp body = Scott $ do
    sBody <- unScott body
    let (bodyText, bodyHead) = case sBody of SoVal t h _ -> (t, h)
        text = "(\\" <> T.unpack name <> " -> " <> bodyText <> ")"
    pure $ SoVal text bodyHead []

  -- Value-level application: parenthesise the whole call so the
  -- result is safe in any position (ctor arg, case scrutinee,
  -- nested application).  Function and arg texts are inlined
  -- as-is; lambda functions and nested apps already self-parens
  -- themselves, so no further wrapping is needed.
  --
  -- Data-type propagation: take f's data type if known, else x's
  -- as a heuristic fallback.  Pure functions over Scott-encoded
  -- data (e.g., 'fib :: Nat -> Nat') have a knowable return type
  -- through 'valLam's body-propagation, so 'fib n' inherits Just
  -- "Nat" via f.  For unknown-return functions (e.g., a bare
  -- 'valVar' whose return type the carrier doesn't track yet),
  -- x's data type is a sound guess for identity-shaped cases
  -- like '(\\x -> x) T'.  Tracking variable return types in the
  -- env would tighten this, but for the current corpus the
  -- heuristic suffices.
  valApp _ann _appPath f x = Scott $ do
    sF <- unScott f
    sX <- unScott x
    let (fText, fHead) = case sF of SoVal t h _ -> (t, h)
        (xText, xHead) = case sX of SoVal t h _ -> (t, h)
        resultHead = case fHead of
          Just _  -> fHead
          Nothing -> xHead
    pure $ SoVal ("(" <> fText <> " " <> xText <> ")") resultHead []
