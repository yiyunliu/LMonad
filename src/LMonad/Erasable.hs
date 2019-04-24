{-@ LIQUID "--reflection"  @-}

module LMonad.Erasable where
import LMonad.Label
import LMonad.TCB

{-@ class measure erase :: (Label l) => l : l -> a -> a @-}
{-@ class Erasable a where
  erase :: forall l. (Label l) => l : l -> a -> {ea : a | erase l ea == ea}
@-}


class Erasable a where
  erase :: (Label l) => l -> a -> a


instance Erasable Int where
  erase = erase'

instance (Erasable a, Label l) => Erasable (Labeled l a) where
  erase = undefined -- can't unify the two labels




{-@ reflect erase' @-}
{-@ erase' :: (Label l) => l : l -> Int -> {ea : Int | erase' l ea == ea} @-}
erase' :: (Label l) => l -> Int -> Int
erase' _ a = a



