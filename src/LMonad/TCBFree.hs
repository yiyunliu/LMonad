{-# LANGUAGE DeriveFunctor #-}
module LMonad.TCBFree where
import Data.Functor.Identity
import Control.Monad.Free
import LMonad.TCB

data Erasable a = Hole | Observable a
  deriving (Eq, Functor)


type FreeLMonad l m = Free (LMonadT l m) 


getCurrentLabelF :: (Label l, LMonad m) => FreeLMonad l m l
getCurrentLabelF = liftF getCurrentLabel



-- erase :: (Label l)
