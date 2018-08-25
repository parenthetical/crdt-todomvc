{-# LANGUAGE DeriveGeneric #-}
module Crdt.Dot where
import GHC.Generics (Generic)
import Data.Serialize

type Seq = Int -- should be a positive integer
data Dot i = Dot { actorId :: i
                 , sequence :: Seq }
   deriving (Ord,Eq,Show,Read,Generic)
instance (Serialize i) => Serialize (Dot i)
