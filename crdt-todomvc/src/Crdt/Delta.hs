{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs, ScopedTypeVariables, DeriveGeneric #-}

module Crdt.Delta (Id(..),compile,compileLocal) where

import qualified Data.Map as Map
import Data.Map (Map)
--import qualified Data.Map.Merge.Lazy as Map
import Data.Semigroup
import qualified Data.IntMap.Lazy as IntMap
import Control.Monad.State.Strict
  ( MonadState(), modify, get, runState, State, runStateT)
import qualified Data.List as List
import Data.Bifunctor
import Algebra.Lattice (JoinSemiLattice((\/)), joins, BoundedJoinSemiLattice(), bottom)
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Control.Monad.Writer.Lazy
import Control.Monad.Identity
import Crdt.State.Digestable( Digestable(..)
                            , strictlyInflates
                            , minDelta
                            , MaybeDigest(..)
                            )

import Crdt.State.DotStore (DotStore(..))
import Crdt.State.Decomposable
import Crdt.State.Causal (CCrdt(..))
import qualified Crdt.State.DotFun as DF
import qualified Crdt.State.DotMap as DM
import qualified Crdt.State.DotPair as DP
import qualified Crdt.Dot.CausalContext as CC
import Crdt.Dot
import qualified Crdt.AntiEntropyAlgo as A
import qualified Crdt.Local as L

import Crdt.Ast ( Ast(..), Crdt(..),Clearable(..)
                , MonoidMap(..),WrappedLattice(..)
                , CId)

newtype Id i = Id (i,Int)
  deriving (Show,Read,Ord,Eq)

instance CId (Id Int) where
instance CId (Id ()) where

-- FIXME SeqCtr use not OK.
type Ctr a = (State (Int,Int)) a





compile :: (Show i, Read i, Ord i, Ord t, Show t, Read t)
  => Bool
  -> Bool
  -> Bool
  -> Bool
  -> Crdt (Id i) o v
  -> A.Algo t i o v
compile bp rr useAck useDigests (Crdt o v p) =
  case compileAst p of
    Comp mutator query ->
      compile' bp rr useAck useDigests o v mutator
      (maybe mempty id . query . dotStore)

compileLocal :: ()
  => Crdt (Id ()) o v
  -> L.Local o v
compileLocal crdt =
  let A.Algo initState applyOp evalState _ _ =
        compile True True True True crdt
  in L.Local initState (\state op -> applyOp 0 () op state) evalState



data Comp t i o v where
  Comp :: ( DotStore i ds
          , Decomposable ds
          , Show ds, Read ds, Eq ds
          , Monoid v
          ) =>
       { mutator :: t -> i -> o -> CCrdt i ds -> Ctr (CCrdt i ds)
       , query :: ds -> Maybe v
       }
       -> Comp t i o v


-- TODO: Implement stability for state based CRDTs so that Filter can
-- be used.
compileAst :: ( Ord i, Ord t, Show i, Read i, Show t, Read t, Show o, Read o
              , Eq o)
           => Ast (Id i) o v
           -> Comp t i o v
compileAst = \case
  Sgr -> compileSgr
  MonotoneSgr -> compileSgr
  Lat -> compileLat
  Clr always x -> compileClr always (compileAst x)
  Dct x -> compileDct (compileAst x)
  Pair a b -> compilePair (compileAst a) (compileAst b)
  Lww x -> compileLww (compileAst x)
  Conc x -> compileConc (compileAst x)
  MapId f' a -> compileMapId f' (compileAst a)
  Filter f' a -> compileFilter f' (compileAst a)


compileMapId :: (Id i -> o -> o')
             -> Comp t i o' v'
             -> Comp t i o v'
compileMapId f (Comp mutator query) =
  Comp { mutator =
         \t i o ccrdt -> do
           (count,_) <- modify (first (+1)) >> get
           let o' = f (Id (i,count)) o
           mutator t i o' ccrdt
       , query = query
       }

compileFilter :: (v -> Bool)
              -> Comp t i o v
              -> Comp t i o v
compileFilter f (Comp mutator query) =
  Comp { mutator = mutator
       , query = join
                 . fmap (\v -> if f v
                               then Just v
                               else Nothing)
                 . query
       }

compileSgr :: forall t i a. (Ord i, Show i, Read i, Show a, Read a, Eq a
                            , Semigroup a)
  => Comp t i a (Option a)
compileSgr =
  Comp { mutator =
         \_t i a _ -> do
           (_,s) <- modify (second (+1)) >> get
           let dot = Dot i s
           return $ CCrdt (DF.singleton dot a) (CC.singleton dot)
       , query =
         (\(DF.DotFun df) ->
            Just
            . Map.foldMapWithKey
            (\_k -> IntMap.foldMapWithKey (\_k -> Option . Just))
            $ df)
       }

compileLat :: forall t i a. ( BoundedJoinSemiLattice a, Ord i
                            , Show a, Read a, Show i, Read i, Eq a)
  => Comp t i a (WrappedLattice a)
compileLat =
  case compileSgr of
    Comp mutator query ->
      Comp { mutator = \t i -> mutator t i  . WrapLattice
           , query = fmap (option mempty id) . query
           }

compileClr :: ()
  => Bool
  -> Comp t i o v
  -> Comp t i (Clearable o) v
compileClr always Comp{mutator,query} =
  Comp
  { mutator = \t i o' ccrdt@(CCrdt ds _cc) ->
      let clear = (CCrdt bottom (CC.fromDotSet $ dots ds))
      in -- If clear always, join the Do _ and Clear mutators
       case o' of
        Clear ->
          return clear
        Do o'' -> do
          delta <- mutator t i o'' ccrdt
          return (case always of
                    True -> clear \/ delta
                    False -> delta)
  , query = query
  }

compilePair :: ()
  => Comp t i o v
  -> Comp t i o' v'
  -> Comp t i (Either o o') (v,v')
compilePair (Comp mutatora querya) (Comp mutatorb queryb) =
  Comp
  { mutator = \t i o (CCrdt (DP.DotPair (dsa,dsb)) cc) ->
      case o of
        Left o' -> do
          CCrdt dsa' cc' <- mutatora t i o' (CCrdt dsa cc)
          return (CCrdt (DP.DotPair (dsa',bottom)) cc')
        Right o' -> do
          CCrdt dsb' cc' <- mutatorb t i o' (CCrdt dsb cc)
          return (CCrdt (DP.DotPair (bottom,dsb')) cc')
  , query = \dp ->
      case (bimap querya queryb) . DP.getPair $ dp of
        (Nothing,Nothing) -> Nothing
        x -> Just $
             bimap
             (maybe mempty id)
             (maybe mempty id)
             x
  }

compileDct ::
  (Ord k, Show k, Read k)
  => Comp t i o v
  -> Comp t i (k,o) (MonoidMap k v)
compileDct Comp{mutator,query} =
  Comp
  { mutator = \t i (k,o) (CCrdt (DM.DotMap dm) cc) -> do
      (CCrdt ds cc') <-
        mutator t i o (CCrdt (Map.findWithDefault bottom k dm) cc)
      return $ (CCrdt (DM.singleton k ds) cc')
  , query = \m ->
      let m' = Map.mapMaybe query . DM.getMap $ m
          -- TODO: Study this choice implied by "Filter ignores all
          -- history."
      in if Map.null m'
         then Nothing
         else Just . MonoidMap $ m'
  }

compileLww ::
  (Eq t, Ord t, Show i, Read i, Show t, Read t)
  => Comp t i o v
  -> Comp t i o v
compileLww (Comp mutator query) =
  -- FIXME: This will lead to non-continous causal contexts because of
  -- the seqCtr.
  case compileSgr of
    Comp mutator' query' ->
      let getCCrdt =
            \df ->
              case query' df of
                Nothing -> bottom
                -- This case should never occur.
                Just (Option Nothing) -> bottom
                Just (Option (Just es)) ->
                  let maxT = maximum . map fst $ es
                  in joins
                     . map snd
                     . filter ((== maxT) . fst)
                     $ es
      in Comp { mutator =
                  \t i op ccrdt@(CCrdt df _cc) -> do
                    delta <- mutator t i op . getCCrdt $ df
                    mutator' t i [(t,delta)] ccrdt
              , query = query . dotStore . getCCrdt
              }

compileConc :: forall t i o v.
  ()
  => Comp t i o v
  -> Comp t i [o] v
compileConc Comp{mutator,query} =
  Comp
  { mutator =
      \t i (ops::[o]) ccrdt ->
        fmap joins
        . mapM (\op -> mutator t i op ccrdt)
        $ ops
  , query = query
  }


type SeqNum = Int

compile' :: forall t i ds o v o' v'.
  ( Ord i, Show i, Read i, DotStore i ds, Show ds, Read ds
  , Decomposable ds, Eq ds)
  => Bool
  -> Bool
  -> Bool
  -> Bool
  -> (v' -> o -> o')
  -> (v' -> v)
  -> (t -> i -> o' -> CCrdt i ds -> Ctr (CCrdt i ds))
  -> (CCrdt i ds -> v')
  -> A.Algo t i o v
compile' useAck useDigests bp rr o v mutator query =
  let fixMsgsState (msgs, state) = 
        ( map (second show) msgs
        , show state
        )
  in A.Algo
     { A.initAlgoState = show (initState :: Node i (CCrdt i ds))
     , A.receive = \i j msg str ->
         fixMsgsState
         . runIdentity
         . (flip runStateT) (read str :: Node i (CCrdt i ds))
         . execWriterT
         $ receive useAck rr i j (read msg)
     , A.doOp = \t i op str ->
         let state@Node{crdtState,idCtr,seqNum,dotCtr,buffer} =
               read str
             (d,(idCtr',dotCtr')) =
               runState
               (mutator t i (o (query crdtState) op) crdtState)
               (idCtr,dotCtr)
         in show
            $ state { crdtState = d \/ crdtState
                    , buffer = Map.insert seqNum (d,i) buffer
                    , seqNum = seqNum + 1
                    , dotCtr = dotCtr'
                    , idCtr = idCtr'
                    }
     , A.sync = \i is str ->
         fixMsgsState $
         sync bp useAck useDigests i is (read str :: Node i (CCrdt i ds))
     , A.queryState = \str ->
         v
         . query
         . crdtState
         $ (read str :: Node i (CCrdt i ds))
     }

data Node i crdt =
  Node { seqNum :: SeqNum
       , dotCtr :: Int
       , idCtr :: Int
       -- Delta groups with origin node
       , buffer :: Map SeqNum (crdt, i)
       , acks :: Map i SeqNum
       , crdtState :: crdt
       }
  deriving (Show,Read,Eq,Ord,Generic)

instance (Ord i, Serialize i, Serialize crdt) => Serialize (Node i crdt)

data Msg crdt digest
  = Delta crdt SeqNum
  | Digest1 (MaybeDigest digest crdt) SeqNum
  | Digest2 digest crdt SeqNum
  | Ack SeqNum
  deriving (Show,Read,Eq,Ord,Generic)

instance (Serialize crdt, Serialize digest) => Serialize (Msg crdt digest)

-- type M i crdt digest = A.M i (Msg crdt digest) (Node i crdt)

initState :: BoundedJoinSemiLattice crdt => Node i crdt
initState =
  Node { seqNum = 0
       , buffer = Map.empty
       , acks = Map.empty
       , crdtState = bottom
       , dotCtr = -1
       , idCtr = 0
       }


storeAck :: (Ord i, MonadState (Node i crdt) m) => i -> SeqNum -> m ()
storeAck from n =
  modify $ \state@Node{acks} ->
    state { acks = Map.insert from
                   (max (Map.findWithDefault 0 from acks) n)
                   acks }

receive :: (Digestable crdt digest, Decomposable crdt, Ord i)
  => ( MonadWriter [(i, Msg crdt digest)] m
     , MonadState (Node i crdt) m)
  => Bool
  -> Bool
  -> i
  -> i
  -> Msg crdt digest
  -> m ()
receive useAck rr i j msg = do
  Node{crdtState,seqNum,buffer} <- get
  case msg of
    Delta deltaJ n -> do
      when useAck $ tell [(j, Ack n)]
      let delta = minDelta deltaJ (DigestDelta crdtState)
      when (if rr
            then bottom /= delta
            else (deltaJ `strictlyInflates` crdtState)) $
        modify $ \state -> state
        { crdtState = crdtState \/ deltaJ
        , buffer = Map.insert seqNum
                   ( if rr then delta else deltaJ
                   , j )
                   $ buffer
        , seqNum = seqNum + 1 }
    Ack n -> do
      storeAck j n
    Digest1 r n -> do
      let deltaI = minDelta crdtState r
      case r of
        DigestDelta d -> do
          tell [(j, Delta deltaI seqNum)]
          receive useAck rr i j (Delta d n)
        -- TODO: Why is d not used?
        DigestDigest d -> do
          let DigestDigest q = digest crdtState
          tell [(j, Digest2 q deltaI seqNum)]
      unless useAck $ storeAck j seqNum
    Digest2 r deltaJ n -> do
      let deltaI = minDelta crdtState (DigestDigest r)
      tell [(j, Delta deltaI seqNum)]
      unless useAck $ storeAck j seqNum
      receive useAck rr i j (Delta deltaJ n)

sync :: (Digestable crdt digest, Ord i)
--  => (Show i, Show crdt, Show digest)
  => Bool -> Bool -> Bool
  -> i -> [i] -> Node i crdt
  -> ([(i, Msg crdt digest)], Node i crdt)
sync bp useAck useDigests i neighbors state =
 runIdentity . (flip runStateT) state . execWriterT $ do
  Node{buffer,acks} <- get
  unless (Map.null acks) $ do
    let l = List.minimum . Map.elems $ acks
    modify $ \state -> state{buffer = snd . Map.split (l-1) $ buffer}
  Node{crdtState,seqNum,buffer,acks} <- get
  forM_ neighbors $
    (\j -> do
      let ackJ = Map.findWithDefault 0 j acks
      unless (seqNum == ackJ) $ do
        -- TODO add option to turn off digests
        if (Map.null buffer && ackJ < seqNum)
           || (ackJ < (fst . Map.findMin $ buffer))
          then (when (i < j) $ do
                   tell [(j, Digest1 (if useDigests
                                      then (digest crdtState)
                                      else DigestDelta crdtState)
                             seqNum)]
                   unless useAck $ storeAck j seqNum)
          else do let d = joins
                          . List.map fst
                          . List.filter ((\n -> not bp || j /= n) . snd)
                          . List.map (buffer Map.!)
                          $ [ ackJ .. seqNum - 1 ]
                  -- Don't send superfluous messages:
                  when (d /= bottom) $ do
                    tell [(j, Delta d seqNum)]
                    unless useAck $ storeAck j seqNum)
