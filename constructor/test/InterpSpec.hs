{-# LANGUAGE OverloadedStrings #-}

-- | Standalone tests for 'Constructor.Interp'.
--
--   Hand-constructed 'Expr' values exercise the reduction engine
--   without going through the parser.  Phase B of the narrowing plan:
--   verify the interpreter reduces concrete-arg applications, case
--   dispatch, and lambda application; verify it produces 'VStuck'
--   shapes when reduction can't proceed.
module InterpSpec (tests) where

import Constructor.Interp
  ( Arm (..)
  , Expr (..)
  , Pattern (..)
  , Stuck (..)
  , Value (..)
  , interp
  )
import qualified Data.Map.Strict as Map

tests :: [(String, IO Bool)]
tests =
  [ pure_ "ctor reduces to itself" $
      interp Map.empty Map.empty (ECtor "Z" [])
        `shouldBe` VCon "Z" []

  , pure_ "ctor app reduces children" $
      interp Map.empty Map.empty
        (ECtor "S" [ECtor "Z" []])
        `shouldBe` VCon "S" [VCon "Z" []]

  , pure_ "identity lambda applied" $
      interp Map.empty Map.empty
        (EApp (ELam "x" (EVar "x")) (ECtor "Z" []))
        `shouldBe` VCon "Z" []

  , pure_ "case on Z picks first arm" $
      interp Map.empty Map.empty
        (ECase (ECtor "Z" [])
          [ Arm (PCtor "Z" []) (ECtor "Z" [])
          , Arm (PCtor "S" [PWild]) (ECtor "S" [ECtor "Z" []])
          ])
        `shouldBe` VCon "Z" []

  , pure_ "case on S picks second arm; binder binds" $
      interp Map.empty Map.empty
        (ECase (ECtor "S" [ECtor "Z" []])
          [ Arm (PCtor "Z" []) (ECtor "Z" [])
          , Arm (PCtor "S" [PVar "k"]) (EVar "k")
          ])
        `shouldBe` VCon "Z" []

  , pure_ "pickZ Z reduces to Z (via global lookup)" $
      let pickZ = ELam "n"
            (ECase (EVar "n")
              [ Arm (PCtor "Z" [])         (ECtor "Z" [])
              , Arm (PCtor "S" [PWild])    (ECtor "S" [ECtor "Z" []])
              ])
          gs = Map.singleton "pickZ" pickZ
      in interp gs Map.empty (EApp (EVar "pickZ") (ECtor "Z" []))
           `shouldBe` VCon "Z" []

  , pure_ "pickZ (S Z) reduces to S Z" $
      let pickZ = ELam "n"
            (ECase (EVar "n")
              [ Arm (PCtor "Z" [])         (ECtor "Z" [])
              , Arm (PCtor "S" [PWild])    (ECtor "S" [ECtor "Z" []])
              ])
          gs = Map.singleton "pickZ" pickZ
      in interp gs Map.empty
           (EApp (EVar "pickZ") (ECtor "S" [ECtor "Z" []]))
           `shouldBe` VCon "S" [VCon "Z" []]

  , pure_ "free variable produces VStuck SVar" $
      case interp Map.empty Map.empty (EVar "foo") of
        VStuck (SVar "foo") -> True
        _                   -> False

  , pure_ "case on free var produces VStuck SCase" $
      case interp Map.empty Map.empty
             (ECase (EVar "x")
               [ Arm (PCtor "Z" []) (ECtor "Z" []) ]) of
        VStuck (SCase (VStuck (SVar "x")) _) -> True
        _                                    -> False

  , pure_ "@-binder binds whole + recurses inner" $
      interp Map.empty Map.empty
        (ECase (ECtor "S" [ECtor "Z" []])
          [ Arm (PAt "y" (PCtor "S" [PVar "k"]))
                (ECtor "Pair" [EVar "y", EVar "k"])
          ])
        `shouldBe` VCon "Pair"
                     [ VCon "S" [VCon "Z" []]
                     , VCon "Z" []
                     ]

  , pure_ "wildcard matches anything; no binders" $
      interp Map.empty Map.empty
        (ECase (ECtor "S" [ECtor "Z" []])
          [ Arm (PCtor "Z" []) (ECtor "wrong" [])
          , Arm PWild          (ECtor "right" [])
          ])
        `shouldBe` VCon "right" []
  ]

-- | Trivial pure test wrapper: a 'Bool' result lifts to 'IO Bool'.
pure_ :: String -> Bool -> (String, IO Bool)
pure_ name b = (name, pure b)

-- | Tiny boolean assertion: yields 'True' on match, 'False' on
--   mismatch.  Cleaner than wiring HUnit just for this.
shouldBe :: Eq a => a -> a -> Bool
shouldBe a b = a == b
