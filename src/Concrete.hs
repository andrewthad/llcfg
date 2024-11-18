{-# language DuplicateRecordFields #-}
{-# language QuantifiedConstraints #-}
{-# language MultiWayIf #-}
{-# language DataKinds #-}
{-# language MagicHash #-}
{-# language PatternSynonyms #-}
{-# language UnboxedTuples #-}

-- Notes to Self:
--
-- * [Done] Add witnesses of the count of terminal and nonterminal symbols to Cfg.
--   This will make it so that we do not have to thread these around everywhere.
-- * Consider using UnliftedDatatypes for most types defined in this module.
-- * Build follow table
-- * Add fruitfulness analysis
-- * [Done] Add reachability analysis
-- * [Done] Add types that hide the numeric parts of this.
-- * [Done] Implement a grammar parser to make it easier to write tests.
-- * [Done] Implement a parser that turn the tokens into a tree-like structure.
--   This requires that the productions have some sense of identity.
--   Production IDs must appear in this result. Productions probably
--   cannot have their arity tracked though. The size of the annotations
--   on the CFG would explode if that were done.
--   Productions could be given a sense of identity numerically, but we
--   could also just annotate them in a more traditional way. The annotation
--   could be unit, or it could be a number, or it could even be a function
--   that consumes the tokens.
-- * Figure out how to use the machinery in this module to build something
--   that can assemble user-defined types. I think that the easiest way to
--   do this is to first implement the parser that produces a tree of
--   tokens (essentially untyped). Then, walk that tree and apply a
--   per-production reducer to each token sequence. This step requires
--   dynamic typing, but none of the casts should fail. The types should
--   already have been checked, but they are forgotten when we convert
--   the CFG to the form that this module uses.
-- * Consider rewriting ParseTree and ParseProduction. It will be painful
--   to do this. Not sure how important this actually is.
module Concrete
  ( Cfg(..)
  , Cfg_(..)
  , ParseTable(..)
  , ParseTree(..)
  , Production(..)
  , removeUselessProductions
  , buildNullableTable
  , buildFirstSetTable
  , buildParseTable
  , recognize
  , parse
    -- Helpers for testing
  , PlainAnnotation(..)
  , decodeCfg
  ) where

import Control.Monad (when)
import Control.Monad.ST (ST,runST)
import Data.List.Split (splitOn)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT)
import Data.Foldable (traverse_,for_)
import Data.Kind (Type)
import Data.Primitive (SmallArray)
import Data.Functor.Const (Const(Const))
import Data.Char (ord)
import Data.List (dropWhileEnd,dropWhile)
import Data.Foldable (forM_)
import Data.Unlifted (Bool#, pattern True#, pattern False#)
import Arithmetic.Types (Fin,Fin#,Nat#,EitherFin#, pattern EitherFinRight#, pattern EitherFinLeft#)
import Arithmetic.Nat ((<?#), pattern N0#)
import Data.Maybe.Void (pattern JustVoid#)
import Control.Monad.Trans.Except (runExceptT,throwE)
import GHC.Exts (TYPE,RuntimeRep(IntRep))

import qualified Vector.Bit as Bit
import qualified Vector.Lifted as Lifted
import qualified GHC.Exts as Exts
import qualified Vector.Int as Int
import qualified Arithmetic.Types as Arithmetic
import qualified Arithmetic.Nat as Nat
import qualified Arithmetic.Fin as Fin
import qualified GHC.TypeNats as GHC

-- | Representation: The unlifted array has T+1 elements, where
-- T is the number of nonterminals. In this outermost array, the
-- index in the array implies a nonterminal. Each nonterminal may
-- have zero or more productions (the length of the second level
-- of unlifted arrays). And each production is just a sequence of
-- terminals and nonterminals.
--
-- Nonterminals start at zero and go up into the positive numbers.
-- The nonterminals with number zero is considered to be the start.
-- Terminals start at negative one and go down into the negative
-- numbers.
--
-- Type variables:
--
-- * p means production annotation (often: Const ()), argument is the production arity
-- * n means nonterminal count
-- * t means terminal count
data Cfg (p :: GHC.Nat -> Type) t n = Cfg
  { terminalCount :: Nat# t
  , nonterminalCount :: Nat# n
  , grammar :: !(Lifted.Vector n (SmallArray (Production p t n)))
  }

data Cfg_ (p :: GHC.Nat -> Type) = forall (t :: GHC.Nat) (n :: GHC.Nat). Cfg_
  { terminalCount :: Nat# t
  , nonterminalCount :: Nat# n
  , grammar :: !(Lifted.Vector n (SmallArray (Production p t n)))
  }

data ParseTable (p :: GHC.Nat -> Type) (t :: GHC.Nat) (n :: GHC.Nat) = ParseTable
  { terminalCount :: Nat# t
  , nonterminalCount :: Nat# n
  , table :: !(Lifted.Vector n (Lifted.Vector t (ProductionOption p t n)))
  }

instance Eq (ParseTable p t n) where
  ParseTable n t t1 == ParseTable _ _ t2 =
    fmap Lifted.toSmallArray (Lifted.toSmallArray t1)
    ==
    fmap Lifted.toSmallArray (Lifted.toSmallArray t2)

-- A parse tree that can be used to communicate the source position of each
-- symbol in a production.
data ParseTree (p :: GHC.Nat -> Type) (a :: Type)
  = forall (z :: GHC.Nat).
    ParseTreeBranch
      (Nat# z) -- symbol count
      (p z) -- production annotation
      (Lifted.Vector# z (ParseTree p a)) -- symbols
  | ParseTreeLeaf a

data ParseProduction (p :: GHC.Nat -> Type) (a :: Type)
  = forall (z :: GHC.Nat) (i :: GHC.Nat).
    ParseProduction
      (Nat# z) -- symbol count
      (p z) -- production annotation
      (Lifted.Vector# z (ParseTree p a)) -- symbols
      (Nat# i) -- new position in the input

instance (forall (z :: GHC.Nat). Show (p z), Show a) => Show (ParseTree p a) where
  showsPrec d (ParseTreeLeaf m) = showParen (d > 10) $
    showString "ParseTreeLeaf " . showsPrec 11 m
  showsPrec d (ParseTreeBranch a b c) = showParen (d > 10) $
    showString "ParseTreeBranch "
      . showsPrec 11 (Exts.I# (Nat.demote# a))
      . showChar ' '
      . showsPrec 11 b
      . showChar ' '
      . showsPrec 11 (Lifted.toSmallArray (Lifted.Vector c))

-- TODO: Compare the annotations
instance Eq a => Eq (ParseTree p a) where
  ParseTreeLeaf x == ParseTreeLeaf y = x == y
  ParseTreeBranch sz1 ann1 sym1 == ParseTreeBranch sz2 ann2 sym2 =
    case Nat.testEqual# sz1 sz2 of
      JustVoid# _ -> Lifted.toSmallArray (Lifted.Vector sym1) == Lifted.toSmallArray (Lifted.Vector sym2)
      _ -> False
  _ == _ = False


data Production (p :: GHC.Nat -> Type) (t :: GHC.Nat) (n :: GHC.Nat) = forall (z :: GHC.Nat). Production
  { symbolCount :: Nat# z
  , annotation :: p z
  , symbols :: Int.Vector# z (EitherFin# t n)
  }

-- TODO: Compare the annotations as well
instance Eq (Production p t n) where
  Production sz1 ann1 sym1 == Production sz2 ann2 sym2 = case Nat.testEqual# sz1 sz2 of
    JustVoid# eq -> Int.equals sz2 (Int.substitute eq (Int.Vector sym1)) (Int.Vector sym2)
    _ -> False

data ProductionOption (p :: GHC.Nat -> Type) (t :: GHC.Nat) (n :: GHC.Nat)
  = ProductionSome !(Production p t n)
  | ProductionNone

deriving instance Eq (ProductionOption p t n)

data Stack t n = Cons (EitherFin# t n) !(Stack t n) | Empty

parseProductionError :: a
{-# noinline parseProductionError #-}
parseProductionError = errorWithoutStackTrace "llcfg.parseProduction: whoops"

parse ::
     ParseTable p t n -- parse table
  -> Fin# n -- start nonterminal
  -> Nat# z -- length of the input
  -> Int.Vector z (Fin# t) -- the input reduced to terminal indices
  -> Lifted.Vector z a -- the complete input
  -> Either () (ParseTree p a)
parse theTable@ParseTable{table} start len terminals tokens =
  let !row = Lifted.index table start
   in case N0# <?# len of
        JustVoid# lt -> case Lifted.index row (Int.index terminals (Fin.construct# lt N0#)) of
          ProductionNone -> Left ()
          ProductionSome p -> case parseProduction theTable len terminals tokens N0# p of
            Left err -> Left err
            Right (ParseProduction sub0 sub1 sub2 _) -> Right (ParseTreeBranch sub0 sub1 sub2)
        _ -> error "parse: figure this case out. might need the follow table to check for nullable"

parseProduction :: forall n t z p i (a :: Type).
     ParseTable p t n -- the parse table
  -> Nat# z -- length of the input
  -> Int.Vector z (Fin# t) -- the input reduced to terminal indices
  -> Lifted.Vector z a -- the complete input
  -> Nat# i -- index into the input
  -> Production p t n -- production that has been decided on. parse all of it
  -> Either () (ParseProduction p a)
parseProduction table len terminals tokens ix (Production symbolCount ann symbols) = runST $ do
  dst <- Lifted.initialized symbolCount parseProductionError
  parseProductionAt table len terminals tokens ix symbolCount N0# ann symbols dst

parseProductionAt :: forall n t z p i x (s :: Type) (r :: GHC.Nat) (a :: Type).
     ParseTable p t n -- the parse table
  -> Nat# z -- length of the input
  -> Int.Vector z (Fin# t) -- the input reduced to terminal indices
  -> Lifted.Vector z a -- the complete input
  -> Nat# i -- index into the input
  -> Nat# r -- length of symbols to match in current production
  -> Nat# x -- index into the current production being matched
  -> p r -- current production
  -> Int.Vector# r (EitherFin# t n) -- symbols that the current production matches
  -> Lifted.MutableVector s r (ParseTree p a) -- buffer for results
  -> ST s (Either () (ParseProduction p a))
parseProductionAt table@ParseTable{table=tableContents} len terminals tokens ix symbolCount pix ann symbols dst =
  case pix <?# symbolCount of
    JustVoid# pixlt -> do
      let expectation = Int.index# symbols (Fin.construct# pixlt pix)
      case expectation of
        EitherFinLeft# expectedTerminal -> case ix <?# len of
          JustVoid# lt -> do
            let actualTerminal = Int.index terminals (Fin.construct# lt ix)
            if Fin.equals# expectedTerminal actualTerminal
              then do
                let token = Lifted.index tokens (Fin.construct# lt ix)
                Lifted.write dst (Fin.construct# pixlt pix) (ParseTreeLeaf token)
                parseProductionAt table len terminals tokens (Nat.succ# ix) symbolCount (Nat.succ# pix) ann symbols dst
              else pure (Left ())
        EitherFinRight# expectedNonterminal -> case ix <?# len of
          JustVoid# lt -> do
            let actualTerminal = Int.index terminals (Fin.construct# lt ix)
            case Lifted.index (Lifted.index tableContents expectedNonterminal) actualTerminal of
              ProductionNone -> pure (Left ())
              ProductionSome p -> case parseProduction table len terminals tokens ix p of
                Left err -> pure (Left err)
                Right (ParseProduction sub0 sub1 sub2 ix') -> do
                  Lifted.write dst (Fin.construct# pixlt pix) (ParseTreeBranch sub0 sub1 sub2)
                  parseProductionAt table len terminals tokens ix' symbolCount (Nat.succ# pix) ann symbols dst
        _ -> errorWithoutStackTrace "llcfg.parseProductionAt: impossible"
    _ -> do
      -- We have reached the end of the production. The destination buffer
      -- is fully initialized.
      Lifted.Vector dst' <- Lifted.unsafeFreeze dst
      pure (Right (ParseProduction symbolCount ann dst' ix))

recognize :: forall n t p.
     Fin# n -- nonterminal to start at (probably zero)
  -> ParseTable p t n
  -> Int.Vector_ (Fin# t)
  -> Bool
recognize start ParseTable{table} (Int.Vector_ len tokens) = go N0# (Cons (EitherFinRight# start) Empty)
  where
  go :: forall (i :: GHC.Nat). Nat# i -> Stack t n -> Bool
  go ix s0 = case s0 of
    Empty -> case Nat.testEqual# ix len of
      JustVoid# _ -> True
      _ -> False -- encountered leftovers
    Cons symbol s1 -> case symbol of
      EitherFinRight# nonterminal -> case ix <?# len of
        JustVoid# lt ->
          let token = Int.index# tokens (Fin.construct# lt ix)
           in case Lifted.index (Lifted.index table nonterminal) token of
                ProductionSome (Production sz _ symbols) -> go ix (pushSymbols sz symbols s1)
                ProductionNone -> False
        -- Note: This is incorrect in cases where the last nonterminal
        -- can be empty. Currently, the parse table does not include
        -- information about what productions are possible when EOF
        -- is encountered. Change this when that happens.
        _ -> False
      EitherFinLeft# terminal -> case ix <?# len of
        JustVoid# lt ->
          let token = Int.index# tokens (Fin.construct# lt ix)
           in if Fin.equals# token terminal
                then go (Nat.succ# ix) s1
                else False
        _ -> False
      _ -> errorWithoutStackTrace "llcfg.recognize: impossible"

pushSymbols ::
     Nat# z
  -> Int.Vector# z (EitherFin# t n)
  -> Stack t n
  -> Stack t n
pushSymbols z v s = Int.foldr Cons s z (Int.Vector v)

-- Parse table is a 2d matrix where the elements are productions.
-- This fails if the grammar is not LL(1).
--
-- Adapting this algorithm from StackOverflow:
--
-- foreach(A -> α in the grammar):
--   write A -> α in T[A,b], ∀  b ∈ first(α);
--   if ( ℇ ∈ first(α) ):
--     write A -> α in T[A,x], ∀ x ∈ follow(A);
buildParseTable ::
     Cfg p t n
  -> Either () (ParseTable p t n)
buildParseTable cfg@(Cfg{nonterminalCount=n,terminalCount=t,grammar}) = runST $ do
  let nullableTable = buildNullableTable cfg
      firstSetTable = buildFirstSetTable nullableTable cfg
  mutablePlaceholder <- Lifted.initialized t ProductionNone
  table <- Lifted.initialized n mutablePlaceholder
  Fin.ascendM_# n $ \fin -> do
    Lifted.initialized t ProductionNone >>= Lifted.write table fin
  runExceptT $ do
    -- Now the table is initialized and there is no aliasing
    Lifted.itraverse_
      (\nonterminal productions -> traverse_
        (\productionVector@(Production sz _ production) -> do
          let set = productionFirstSet t nullableTable firstSetTable sz production
          Fin.ascendM_# t $ \fin -> do
            case Bit.index set fin of
              True# -> do
                nonterminalRow <- lift $ Lifted.read table nonterminal
                opt <- lift $ Lifted.read nonterminalRow fin
                case opt of
                  ProductionNone -> lift $ Lifted.write nonterminalRow fin (ProductionSome productionVector)
                  ProductionSome{} -> throwE ()
              _ -> pure ()
          -- Note: Right here, I should check if epsilon is in the
          -- first set and then do something with the follow set if
          -- it is.
        ) productions
      ) n grammar
    lift $ do
      let immutablePlaceholder = Lifted.replicate t ProductionNone
      final <- Lifted.initialized n immutablePlaceholder
      Fin.ascendM_# n $ \fin -> do
        row <- Lifted.read table fin
        Lifted.write table fin mutablePlaceholder
        row' <- Lifted.unsafeFreeze row
        Lifted.write final fin row'
      final' <- Lifted.unsafeFreeze final
      pure ParseTable{nonterminalCount=n,terminalCount=t,table=final'}

buildNullableTable :: Cfg p t n -> Bit.Vector n Bool#
buildNullableTable cfg@Cfg{nonterminalCount=n} = go (1000 :: Word) (Bit.replicate n False#)
  where
  go !0 !_ = error "nullableTable: too many steps to reach a fixed point"
  go !counter !table0 =
    let table1 = nullableTableStep cfg table0
     in if Bit.equals n table1 table0
          then table1
          else go (counter - 1) table1

-- | This removes unused productions, but it does not remove nonterminals
-- that lack productions.
removeUselessProductions :: Cfg p t n -> Cfg p t n
removeUselessProductions cfg0 =
  let fruitful = buildFruitfulnessTable cfg0
      cfg1 = selectNonterminals fruitful cfg0
      reachable = buildReachabilityTable cfg1
      cfg2 = selectNonterminals reachable cfg1
   in cfg2

-- Keep all the nonterminals that are set to True in the bit vector
-- Discard the others by setting their productions to the empty string
selectNonterminals ::
     Bit.Vector n Bool#
  -> Cfg p t n
  -> Cfg p t n
selectNonterminals reachable cfg@Cfg{nonterminalCount=n,terminalCount=t,grammar} =
  case Bit.allEqTrue n reachable of
    True -> cfg
    False -> Cfg
      { nonterminalCount = n
      , terminalCount = t
      , grammar = runST $ do
          dst <- Lifted.thaw n grammar
          Fin.ascendM_# n $ \terminal -> do
            case Bit.index reachable terminal of
              True# -> pure ()
              _ -> Lifted.write dst terminal mempty
          Lifted.unsafeFreeze dst
      }

buildFruitfulnessTable ::
     Cfg p t n
  -> Bit.Vector n Bool#
buildFruitfulnessTable Cfg{nonterminalCount=n,grammar=Lifted.Vector grammar} = runST $ do
  dst <- Bit.initialized n True#
  Fin.ascendM_# n $ \i -> do
    let productions = Lifted.index# grammar i
    if all (productionReferencesNonterminal i) productions
      then Bit.write dst i False#
      else pure ()
  Bit.unsafeFreeze dst

productionReferencesNonterminal :: Fin# n -> Production p t n -> Bool
productionReferencesNonterminal nt (Production s _ symbols) = Int.any
  (\symbol -> case symbol of
    EitherFinRight# nonterminal -> Fin.equals# nt nonterminal
    _ -> False
  ) s (Int.Vector symbols)

buildReachabilityTable ::
     Cfg p t n
  -> Bit.Vector n Bool#
buildReachabilityTable Cfg{nonterminalCount=n,grammar=Lifted.Vector grammar} = runST $ do
  dst <- Bit.initialized n False#
  Fin.ascendM_# n $ \i -> do
    let productions = Lifted.index# grammar i
    for_ productions $ \(Production s _ symbols) -> do
      Fin.ascendM_# s $ \j -> case Int.index# symbols j of
        EitherFinRight# nonterminal -> Bit.write dst nonterminal True#
        _ -> pure ()
  Bit.unsafeFreeze dst

buildFirstSetTable ::
     Bit.Vector n Bool# -- the nullable table
  -> Cfg p t n
  -> Lifted.Vector n (Bit.Vector t Bool#)
buildFirstSetTable !nullableTable !cfg@Cfg{nonterminalCount=n,terminalCount=t} = go
  (1000 :: Word)
  (Lifted.replicate n (Bit.replicate t False#))
  where
  go !0 !_ = error "buildFirstSetTable: too many steps to reach a fixed point"
  go !counter !table0 =
    let table1 = firstTableStep nullableTable cfg table0
     in if Lifted.foldrZip (\x y acc -> Bit.equals t x y && acc) True n table1 table0
          then table1
          else go (counter - 1) table1

firstTableStep :: forall n t (p :: GHC.Nat -> Type).
     Bit.Vector n Bool# -- completely accurate nullable table
  -> Cfg p t n -- the grammar
  -> Lifted.Vector n (Bit.Vector t Bool#) -- old first-set table
  -> Lifted.Vector n (Bit.Vector t Bool#) -- updated first-set table
firstTableStep !nullableTable Cfg{nonterminalCount=n,terminalCount=t,grammar} !table0 = runST $ do
  table <- Lifted.thaw n table0
  Lifted.itraverse_
    (\nonterminal productions -> traverse_
      (\(Production sz _ production) -> do
        oldFirstSet <- Lifted.read table nonterminal
        let newFirstSet = productionFirstSet t nullableTable table0 sz production
        -- I am not certain that it is necessary to do this. I think the
        -- new set should always be a superset of the old set. But I
        -- am not completely confident in this.
        let newFirstSet' = Bit.zipOr t newFirstSet oldFirstSet
        Lifted.write table nonterminal newFirstSet'
      ) productions
    ) n grammar
  Lifted.unsafeFreeze table

productionFirstSet :: forall n t z.
     Nat# t -- number of terminals
  -> Bit.Vector n Bool# -- completely accurate nullable table
  -> Lifted.Vector n (Bit.Vector t Bool#) -- first-set table
  -> Nat# z -- number of symbols in this production
  -> Int.Vector# z (EitherFin# t n) -- the production
  -> Bit.Vector t Bool#
productionFirstSet t nullableTable firstSetTable sz production =
  let go :: forall (m :: GHC.Nat). Nat# m -> Bit.Vector t Bool# -> Bit.Vector t Bool#
      go !ix !acc = case ix <?# sz of
        JustVoid# lt ->
          let fin = Fin.construct# lt ix
              symbol = Int.index# production fin
              acc' = Bit.zipOr t acc (symbolFirstSet t firstSetTable symbol)
           in case symbolAcceptsEmpty nullableTable symbol of
                True -> go (Nat.succ# ix) acc'
                _ -> acc'
        _ -> acc
   in go Nat.N0# (Bit.replicate t False#)

-- Enumerate all productions and update the nullable table.
nullableTableStep ::
     Cfg p t n -- the grammar
  -> Bit.Vector n Bool# -- old nullable table
  -> Bit.Vector n Bool# -- updated nullable table
nullableTableStep Cfg{nonterminalCount=n,grammar} !table0 = runST $ do
  table <- Bit.thaw n table0
  Lifted.itraverse_
    (\nonterminal productions -> traverse_
      (\(Production sz _ production) -> do
        when (Int.ifoldl' (\acceptsEmpty _ symbol -> acceptsEmpty && symbolAcceptsEmpty table0 symbol) True sz (Int.Vector production)) $ do
          Bit.write table nonterminal True#
      ) productions
    ) n grammar
  Bit.unsafeFreeze table

symbolAcceptsEmpty :: Bit.Vector n Bool# -> EitherFin# t n -> Bool
symbolAcceptsEmpty table sym = case sym of
  EitherFinRight# nonterminal | True# <- Bit.index table nonterminal -> True
  _ -> False

symbolFirstSet ::
     Nat# t
  -> Lifted.Vector n (Bit.Vector t Bool#)
  -> EitherFin# t n
  -> Bit.Vector t Bool#
symbolFirstSet t !firstSetTable e = case e of
  EitherFinRight# nonterminal -> Lifted.index firstSetTable nonterminal
  EitherFinLeft# terminal -> runST $ do
    dst <- Bit.initialized t False#
    Bit.write dst terminal True#
    Bit.unsafeFreeze dst
  _ -> errorWithoutStackTrace "llcfg.symbolFirstSet: impossible"

decodeProduction ::
     Char
  -> (Int,[Char])
  -> ExceptT () (ST s) (Production PlainAnnotation 26 26)
decodeProduction nonterminalChar (altId, encoded) = do
  case Lifted.fromList encoded of
    Lifted.Vector_ symbolCount encodedSymbols -> do
      dst <- lift $ Int.initialized symbolCount (EitherFinLeft# (Fin.constant# N0# ))
      Fin.ascendM_# symbolCount $ \ix -> do
        let c = Lifted.index# encodedSymbols ix
        if | c >= 'A', c <= 'Z', n <- ord c - ord 'A', Just fin <- Fin.fromInt (Nat.constant @26) n ->
               lift $ Int.write dst ix (EitherFinRight# (Fin.unlift fin))
           | c >= 'a', c <= 'z', n <- ord c - ord 'a', Just fin <- Fin.fromInt (Nat.constant @26) n ->
               lift $ Int.write dst ix (EitherFinLeft# (Fin.unlift fin))
           | otherwise -> throwE ()
      Int.Vector symbols <- lift $ Int.unsafeFreeze dst
      pure Production{symbolCount, annotation = PlainAnnotation nonterminalChar altId, symbols}

data PlainAnnotation :: GHC.Nat -> Type where
  PlainAnnotation :: !Char -> !Int -> PlainAnnotation n

deriving instance Show (PlainAnnotation z)

-- A -> abb | SbA | aB
-- B -> AB | CaB
decodeCfg :: String -> Either () (Cfg PlainAnnotation 26 26)
decodeCfg input0 = runST $ runExceptT $ do
  let n26 = Nat.constant# @26 (# #)
  table <- lift $ Lifted.initialized n26 mempty
  let encodedNonterminals = filter (not . null) (lines input0)
  forM_ encodedNonterminals $ \cs0 -> case cs0 of
    c : cs1 -> do
      nonterminal <- upperToFin c
      let cs2 = dropWhile (==' ') cs1
      case cs2 of
        '-' : '>' : cs3 -> do
          let cs4 = dropWhile (==' ') cs3
          let encodedProductions = fmap (dropWhileEnd (==' ') . dropWhile (==' ')) (splitOn "|" cs4)
          productions <- traverse (decodeProduction c) (zip [0..] encodedProductions)
          let productions' = Exts.fromList productions
          lift $ Lifted.write table (Fin.unlift nonterminal) productions'
        _ -> throwE ()
    _ -> throwE ()
  table' <- lift $ Lifted.unsafeFreeze table
  pure (Cfg n26 n26 table')

upperToFin :: Monad m => Char -> ExceptT () m (Fin 26)
upperToFin c
  | c >= 'A', c <= 'Z', n <- ord c - ord 'A', Just fin <- Fin.fromInt (Nat.constant @26) n = pure fin
  | otherwise = throwE ()
