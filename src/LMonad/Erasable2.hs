{-# LANGUAGE FlexibleInstances #-}
{-@ LIQUID "--reflection"  @-}

module LMonad.Erasable2 where
import LMonad.Label
import LMonad.TCB

{-@ class measure erase :: (Label l) => l : l -> a -> a @-}
{-@ class Erasable a where
  erase :: forall l. (Label l) => l : l -> a -> {ea : a | erase l ea == ea}
@-}


class (Label l) => Erasable l a where
  erase :: l -> a -> a


instance (Label l) => Erasable l Int where
  erase _ a = a

instance (Label l) => Erasable l () where
  erase _ u = u


-- Erasable a => Erasable (Labeled l a + 1)
instance (Label l, Erasable l a) => Erasable l (Maybe (Labeled l a)) where
  erase l mla = do
    Labeled l' a <- mla
    if l' `canFlowTo` l
      then pure (Labeled l' (erase l a))
      else Nothing

instance Label () where

    canFlowTo _ _ = True
    lub _ _ = ()
    glb _ _ = ()
    bottom = ()
  
    lawFlowReflexivity _ = ()
    lawFlowAntisymmetry _ _ = ()
    lawFlowTransitivity _ _ _ = ()
    
    lawGlb _ _ _ _ = ()
    lawLub _ _ _ _ = ()
    lawBot _ = ()

data BoolLabel = Low | High 
  deriving (Eq, Show)

instance Label BoolLabel where

  canFlowTo Low High  = True 
  canFlowTo Low Low   = True
  canFlowTo High High = True 
  canFlowTo High Low  = False 

  glb Low High  = Low 
  glb Low Low   = Low
  glb High High = High 
  glb High Low  = Low 


  lub Low High  = High 
  lub Low Low   = Low
  lub High High = High 
  lub High Low  = High 

  bottom = Low
  lawFlowReflexivity _ = ()
  lawFlowAntisymmetry _ _ = ()
  lawFlowTransitivity _ _ _ = ()
    
  lawGlb _ _ _ _ = ()
  lawLub _ _ _ _ = ()
  lawBot _ = ()


example1 :: Maybe (Labeled () (Labeled () Int))
example1 = Just (Labeled () (Labeled () 1))

example2 :: Maybe (Labeled BoolLabel (Maybe (Labeled BoolLabel Int)))
example2 = Just (Labeled Low (Just (Labeled High 100)))

-- erase Low example2
-- >>> Just (Labeled {labeledLabel = Low, labeledValue = Nothing})
-- erase High example2
-- >>> Just (Labeled {labeledLabel = Low, labeledValue = Just (Labeled {labeledLabel = High, labeledValue = 100})})
