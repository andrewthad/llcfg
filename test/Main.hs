{-# language BangPatterns #-}
{-# language TypeApplications #-}
{-# language OverloadedLists #-}
{-# language UnboxedTuples #-}
{-# language PatternSynonyms #-}
{-# language DataKinds #-}
{-# language MagicHash #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}

import Arithmetic.Nat (pattern N0#, pattern N1#, pattern N2#, pattern N3#, pattern N4#, pattern N5#)
import Control.Monad.ST (stToIO)
import Data.Char (ord)
import Arithmetic.Types (Fin#, Nat#, EitherFin#, pattern EitherFinRight#, pattern EitherFinLeft#)
import Concrete (Cfg(Cfg), Production(..),buildNullableTable, buildFirstSetTable, buildParseTable, recognize)
import Concrete (ParseTable, ParseTree(ParseTreeLeaf,ParseTreeBranch),PlainAnnotation(PlainAnnotation), decodeCfg, parse)
import Concrete (removeUselessProductions,showCfg)
import Control.Monad (when)
import Data.Unlifted (Bool#, pattern True#, pattern False#)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.HUnit ((@=?))
import Data.Proxy (Proxy(Proxy))

import qualified Arithmetic.Fin as Fin
import qualified Arithmetic.Nat as Nat
import qualified Arithmetic.Lt as Lt
import qualified Test.Tasty.HUnit as THU
import qualified Vector.Bit as Bit
import qualified GHC.TypeNats as GHC
import qualified Vector.Int as Int
import qualified Vector.Lifted as Lifted

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ testGroup "nullability"
    [ THU.testCase "A" $
        let table = buildNullableTable cfgA
         in case Bit.equals N4# table expectedNullabilityCfgA of
              True -> pure ()
              False -> fail $
                "\nExpected:\n" ++ showBoolVector N4# expectedNullabilityCfgA ++ "\n" ++
                "\nGot:\n" ++ showBoolVector N4# table ++ "\n"
    ]
  , testGroup "first-set"
    [ THU.testCase "A" $
        let table = buildFirstSetTable expectedNullabilityCfgA cfgA
         in case firstSetTableEquals N4# N3# table expectedFirstSetCfgA of
              True -> pure ()
              False -> fail $
                "\nExpected:\n" ++ showFirstSet N4# N3# expectedFirstSetCfgA ++ "\n" ++
                "\nGot:\n" ++ showFirstSet N4# N3# table ++ "\n"
    ]
  , testGroup "recognize"
    [ THU.testCase "A" $ case buildParseTable cfgA of
        Left _ -> fail "Could not build parse table"
        Right table -> 
          let !ta = Fin.constant# N0# :: Fin# 3
              !tb = Fin.constant# N1# :: Fin# 3
              !tc = Fin.constant# N2# :: Fin# 3
           in True @=? recognize (Fin.constant# N0#) table (Int.construct4_ tb tb ta tc)
    , THU.testCase "B" $ let cfgB' = removeUselessProductions cfgB in case buildParseTable (removeUselessProductions cfgB') of
        Left _ -> fail $
          "Could not build parse table.\nUnsimplified CFG\n" ++ showCfg cfgB ++
          "Simplified CFG:\n" ++ showCfg cfgB'
        Right table -> 
          let !ta = Fin.constant# N0# :: Fin# 5
              !tb = Fin.constant# N1# :: Fin# 5
           in True @=? recognize (Fin.constant# N0#) table (Int.construct7_ tb ta tb tb ta tb tb)
    , testGroup "decoded"
      [ THU.testCase "P" $ do
          table <- loadAlphaTableFromString "A -> abcd | bb" >>= forceBuildParseTable
          sentence <- loadAlphaSentenceFromString "bb"
          True @=? recognize (Fin.constant# N0#) table (discardTokens sentence)
      , THU.testCase "Q" $ do
          table <- loadAlphaTableFromString "A -> abcd | bb" >>= forceBuildParseTable
          sentence <- loadAlphaSentenceFromString "abbcd"
          False @=? recognize (Fin.constant# N0#) table (discardTokens sentence)
      ]
    , testGroup "parse"
      [ THU.testCase "T" $ do
          table <- loadAlphaTableFromString "A -> abcd | bb" >>= forceBuildParseTable
          AlphaSentence n x y <- loadAlphaSentenceFromString "bb"
          id $
            Right (ParseTreeBranch N2# (PlainAnnotation 'A' 1) (Lifted.construct2# (ParseTreeLeaf 'b') (ParseTreeLeaf 'b')))
            @=?
            parse table (Fin.constant# N0#) n x y
      , THU.testCase "U" $ do
          table <- loadAlphaTableFromString "A -> aBa | bb \nB -> c | d" >>= forceBuildParseTable
          AlphaSentence n x y <- loadAlphaSentenceFromString "ada"
          id $
            Right
              (ParseTreeBranch N3# (PlainAnnotation 'A' 0)
                (Lifted.construct3#
                  (ParseTreeLeaf 'a')
                  (ParseTreeBranch N1# (PlainAnnotation 'B' 1) (Lifted.construct1# (ParseTreeLeaf 'd')))
                  (ParseTreeLeaf 'a')
                )
              )
            @=?
            parse table (Fin.constant# N0#) n x y
      ]
    ]
  ]

loadAlphaTableFromString :: String -> IO (Cfg PlainAnnotation 26 26)
loadAlphaTableFromString s = case decodeCfg s of
  Left _ -> fail "Could not decode CFG from string"
  Right cfg -> pure cfg

data AlphaSentence = forall (z :: GHC.Nat). AlphaSentence
  { size :: Nat# z
  , terminals :: !(Int.Vector z (Fin# 26))
  , tokens :: !(Lifted.Vector z Char)
  }

discardTokens :: AlphaSentence -> Int.Vector_ (Fin# 26)
discardTokens AlphaSentence{size,terminals} = Int.Vector_ size (Int.unlift terminals)

loadAlphaSentenceFromString :: String -> IO AlphaSentence
loadAlphaSentenceFromString input = do
  case Lifted.fromList input of
    Lifted.Vector_ terminalCount encodedTerminals -> do
      dst <- stToIO (Int.initialized terminalCount (Fin.constant# N0# ))
      Fin.ascendM_# terminalCount $ \ix -> do
        let c = Lifted.index# encodedTerminals ix
        if | c >= 'a', c <= 'z', n <- ord c - ord 'a', Just fin <- Fin.fromInt (Nat.constant @26) n ->
               stToIO (Int.write dst ix (Fin.unlift fin))
           | otherwise -> fail "Could not decode sentence from string"
      dst' <- stToIO (Int.unsafeFreeze dst)
      pure (AlphaSentence terminalCount dst' (Lifted.Vector encodedTerminals))

forceBuildParseTable :: Cfg p t n -> IO (ParseTable p t n)
forceBuildParseTable cfg = case buildParseTable cfg of
  Left _ -> fail "Could not build parse table"
  Right table -> pure table

showBoolVector :: Nat# n -> Bit.Vector n Bool# -> String
showBoolVector n v = Bit.ifoldl'
  (\acc _ b -> acc ++ ", " ++ case b of {True# -> "True"; _ -> "False"}
  )  "" n v

showFirstSet :: Nat# n -> Nat# t -> Lifted.Vector n (Bit.Vector t Bool#) -> String
showFirstSet n t v = Lifted.ifoldl'
  (\acc _ bools -> acc ++ ", {" ++ showBoolVector t bools ++ "}"
  )  "" n v

-- This is the grammar:
--
-- S -> ABaC
-- A -> B
-- B -> b | ε
-- C -> c | ε
cfgA :: Cfg Proxy 3 4
cfgA = Cfg N3# N4# $ Lifted.construct4
  [mkp $ Int.construct4_ ntA ntB ta ntC]
  [mkp $ Int.construct1_ ntB]
  [mkp $ Int.construct1_ tb, mkp $ Int.empty_]
  [mkp $ Int.construct1_ tc, mkp $ Int.empty_]
  where
  -- Note: ntS is not defined because it is unused.
  !ntA = EitherFinRight# (Fin.constant# N1#) :: EitherFin# 3 4
  !ntB = EitherFinRight# (Fin.constant# N2#) :: EitherFin# 3 4
  !ntC = EitherFinRight# (Fin.constant# N3#) :: EitherFin# 3 4
  !ta = EitherFinLeft# (Fin.constant# N0#) :: EitherFin# 3 4
  !tb = EitherFinLeft# (Fin.constant# N1#) :: EitherFin# 3 4
  !tc = EitherFinLeft# (Fin.constant# N2#) :: EitherFin# 3 4

expectedNullabilityCfgA :: Bit.Vector 4 Bool#
expectedNullabilityCfgA = Bit.construct4 False# True# True# True#

-- Expected First Sets:
--
-- S -> {ab}
-- A -> {b}
-- B -> {b}
-- C -> {c}
expectedFirstSetCfgA :: Lifted.Vector 4 (Bit.Vector 3 Bool#)
expectedFirstSetCfgA = Lifted.construct4
  (Bit.construct3 True# True# False#)
  (Bit.construct3 False# True# False#)
  (Bit.construct3 False# True# False#)
  (Bit.construct3 False# False# True#)

firstSetTableEquals :: Nat# n -> Nat# t -> Lifted.Vector n (Bit.Vector t Bool#) -> Lifted.Vector n (Bit.Vector t Bool#) -> Bool
firstSetTableEquals n t table0 table1 =
  Lifted.foldrZip (\x y acc -> Bit.equals t x y && acc) True n table1 table0

-- This grammar is from https://www.cs.scranton.edu/~mccloske/courses/cmps260/cfg_remove_useless.html
-- This is used to test that fruitfulness analysis and useless rule pruning
-- are working.
--
-- S -> aSa | bB | bAA    (1) (2) (3)
-- A -> abb | SbA | aB 	  (4) (5) (6)
-- B -> AB | CaB          (7) (8) (note: not fruitful)
-- C -> cC | Sa | bD 	  (9) (10) (11) (note: unreachable)
-- D -> dD | e 	          (12) (13) (note: unreachable)
--
-- Examples of accepted strings:
--
-- * babbabb
cfgB :: Cfg Proxy 5 5
cfgB = Cfg N5# N5# $ Lifted.construct5
  [mkp $ Int.construct3_ ta ntS ta, mkp $ Int.construct2_ tb ntB, mkp $ Int.construct3_ tb ntA ntA]
  [mkp $ Int.construct3_ ta tb tb, mkp $ Int.construct3_ ntS tb ntA, mkp $ Int.construct2_ ta ntB]
  [mkp $ Int.construct2_ ntA ntB, mkp $ Int.construct3_ ntC ta ntB]
  [mkp $ Int.construct2_ tc ntC, mkp $ Int.construct2_ ntS ta, mkp $ Int.construct2_ tb ntD]
  [mkp $ Int.construct2_ td ntD, mkp $ Int.construct1_ te]
  where
  !ntS = EitherFinRight# (Fin.constant# N0#) :: EitherFin# 5 5
  !ntA = EitherFinRight# (Fin.constant# N1#) :: EitherFin# 5 5
  !ntB = EitherFinRight# (Fin.constant# N2#) :: EitherFin# 5 5
  !ntC = EitherFinRight# (Fin.constant# N3#) :: EitherFin# 5 5
  !ntD = EitherFinRight# (Fin.constant# N4#) :: EitherFin# 5 5
  !ta = EitherFinLeft# (Fin.constant# N0#) :: EitherFin# 5 5
  !tb = EitherFinLeft# (Fin.constant# N1#) :: EitherFin# 5 5
  !tc = EitherFinLeft# (Fin.constant# N2#) :: EitherFin# 5 5
  !td = EitherFinLeft# (Fin.constant# N3#) :: EitherFin# 5 5
  !te = EitherFinLeft# (Fin.constant# N4#) :: EitherFin# 5 5

mkp :: Int.Vector_ (EitherFin# t n) -> Production Proxy t n
mkp (Int.Vector_ sz v) = Production sz Proxy v
