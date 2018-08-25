{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Crdt.AntiEntropyAlgo
  (
   Algo(..)
  )
where

data Algo t i o v where
  Algo ::
    { initAlgoState :: String
    , doOp :: t -> i -> o -> String -> String
    , queryState :: String -> v
    , receive :: i -> i -> String -> String -> ([(i,String)], String)
    , sync :: i -> [i] -> String -> ([(i,String)], String)
    }
    -> Algo t i o v
