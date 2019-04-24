{-# LANGUAGE DeriveFunctor #-}
{-@ LIQUID "--reflection"  @-}
-- Some work derived from [LIO](http://hackage.haskell.org/package/lio-eci11), copyrighted under GPL.
--
-- Modifications by James Parker in 2014.

{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeFamilies #-}

-- Only trusted code should import this module. 

module LMonad.TCB (
        module Export
      , LMonad (..)
      , LMonadT(..)
      , runLMonad
      , runLMonadWith
      , lLift
      , getCurrentLabel
      , getClearance
      , lubCurrentLabel
      , canSetLabel
      , setLabel
      , taintLabel
      , taintLabels
      , setClearance
      , raiseClearanceTCB
      , declassifyTCB
      , declassifyNoChecksTCB
      , lowerLabelTCB
      , Labeled(..)
      , Lattice(..)
      , label
      , LState(..)
      , unlabel
      , canUnlabel
      , labelOf
      , toLabeled
      , ToLabel(..)
      , swapBase
    ) where
import Control.Applicative
import Control.Exception.Base
import Control.Exception.Enclosed
import Control.Monad
import Control.Monad.Base
import Control.DeepSeq (NFData)
import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.State
import Data.Monoid
import Prelude

import LMonad.Label as Export

class Monad m => LMonad m where
    lFail :: m a
    lAllowLift :: m Bool
    -- lLift???

data Lattice = Top | Bottom

data LState l = LState {
        _lStateLabel :: !l
      , _lStateClearance :: !l
    }

-- | Type class to convert a given type to a given label.
class ToLabel t l where
    toConfidentialityLabel :: t -> l
    toIntegrityLabel :: t -> l

-- Transformer monad that wraps the underlying monad and keeps track of information flow. 
data LMonadT l m a = LMonadT {
        lMonadTState :: (StateT (LState l) m a)
    }

instance (Label l, LMonad m) => Monad (LMonadT l m) where
    (LMonadT ma) >>= f = 
        LMonadT $ ma >>= (lMonadTState . f)
        -- LMonadT $ do
        -- a <- ma
        -- let (LMonadT mb) = f a
        -- mb
    return = LMonadT . return
    fail _ = LMonadT $ lift lFail

instance (Label l, LMonad m, Functor m) => Functor (LMonadT l m) where
    fmap f (LMonadT ma) = LMonadT $ fmap f ma

instance (Label l, LMonad m, Functor m) => Applicative (LMonadT l m) where
    pure = return
    (<*>) = ap
    
instance (Label l, LMonad m, MonadIO m) => MonadIO (LMonadT l m) where
    liftIO ma = lLift $ liftIO ma

instance (LMonad m, Label l, Functor m, MonadBase IO m) => MonadBase IO (LMonadT l m) where
    liftBase = lLift . liftBase

instance (Label l, LMonad m, MonadThrow m) => MonadThrow (LMonadT l m) where
    throwM = lLift . throwM

newtype StMT l m a = StMT {unStMT :: StM (StateT (LState l) m) a}

-- TODO: This allows replay attacks. Ie, malicious code could reset the current label or clearance to a previous value. 
--     This is needed for Database.Persist.runPool
instance (LMonad m, Label l, MonadBaseControl IO m) => MonadBaseControl IO (LMonadT l m) where
    -- newtype StM (LMonadT l m) a = StMT {unStMT :: StM (StateT (LState l) m) a}
    type StM (LMonadT l m) a = StMT l m a
    liftBaseWith f = LMonadT $ liftBaseWith $ \run -> f $ liftM StMT . run . lMonadTState
    restoreM = LMonadT . restoreM . unStMT



instance (LMonad m, Label l, Semigroup (m a)) => Semigroup (LMonadT l m a) where
    a <> b = a >> b

instance (LMonad m, Label l, Monoid (m a)) => Monoid (LMonadT l m a) where
    mempty = lLift mempty
--    do
--        a' <- a 
--        b' <- b
--        return $ mappend a b
    
-- Runs the LMonad with the given current label and clearance.
runLMonadWith :: (Label l, LMonad m) => l -> l -> LMonadT l m a -> m a
runLMonadWith label clearance (LMonadT lm) = 
    evalStateT lm $ LState label clearance

-- Runs the LMonad with bottom as the initial label and clearance. 
runLMonad :: (Label l, LMonad m) => LMonadT l m a -> m a
runLMonad (LMonadT lm) = 
    let s = LState bottom bottom in
    evalStateT lm s

-- class LMonadTrans t where 
--     lift :: (LMonad m) => m a -> t m a
-- instance (Label l) => MonadTrans (LMonadT l) where
--     -- lift :: (Monad m, LMonad m) => m a -> LMonadT l m a
--     lift m = LMonadT $ lift m

lLift :: (Label l, LMonad m) => m a -> LMonadT l m a
lLift ma = LMonadT $ do
    allow <- lift lAllowLift
    if allow then
        lift ma
    else
        lift lFail


-- fullEraseGetCurrentLabel :: (Label l) => l -> LMonadT l Maybe l
-- fullEraseGetCurrentLabel l = do
--   eraseCheckPoint l
--   lc <- getCurrentLabel
--   eraseCheckPoint l
--   return lc

-- postEraseGetCurrentLabel :: (Label l) => l -> LMonadT l Maybe l
-- postEraseGetCurrentLabel l = do
--   lc <- getCurrentLabel
--   eraseCheckPoint l
--   return lc


getCurrentLabel :: (Label l, LMonad m) => LMonadT l m l
getCurrentLabel = LMonadT $ do
    (LState label _) <- get
    return label

lubCurrentLabel :: (Label l, LMonad m) => l -> LMonadT l m l
lubCurrentLabel l = do
    getCurrentLabel >>= (return . (lub l))

getClearance :: (Label l, LMonad m) => LMonadT l m l
getClearance = LMonadT $ do
    (LState _ clearance) <- get
    return clearance

canAlloc :: (Label l, LMonad m) => l -> StateT (LState l) m Bool
canAlloc l = do
    (LState label clearance) <- get
    return $ canFlowTo label l && canFlowTo l clearance

guardAlloc :: (Label l, LMonad m) => l -> StateT (LState l) m ()
guardAlloc l = do
    guard <- canAlloc l
    unless guard $ 
        lift lFail

canSetLabel :: (Label l, LMonad m) => l -> LMonadT l m Bool
canSetLabel = LMonadT . canAlloc

setLabel :: (Label l, LMonad m) => l -> LMonadT l m ()
setLabel l = do
    LMonadT $ guardAlloc l
    setLabelTCB l

setLabelTCB :: (Label l, LMonad m) => l -> LMonadT l m ()
setLabelTCB l = LMonadT $ do
    (LState _ clearance) <- get
    put $ LState l clearance

taintLabels :: (Label l, LMonad m) => [l] -> LMonadT l m ()
taintLabels [] = return ()
taintLabels (h:t) = do
    let l' = foldr (\l acc -> l `lub` acc) h t
    taintLabel l'

taintLabel :: (Label l, LMonad m) => l -> LMonadT l m ()
taintLabel l = do
    lM' <- taintHelper l
    case lM' of
        Nothing ->
            LMonadT $ lift lFail
        Just l' -> do
            setLabelTCB l'

    -- lubCurrentLabel l >>= setLabel

-- canTaintLabel :: (Label l, LMonad m) => l -> LMonadT l m Bool
-- canTaintLabel l = do
--     lubCurrentLabel l >>= (LMonadT . canAlloc)

setClearanceTCB :: (Label l, LMonad m) => l -> StateT (LState l) m ()
setClearanceTCB c = do
    (LState label _) <- get
    put $ LState label c
    
setClearance :: (Label l, LMonad m) => l -> LMonadT l m ()
setClearance c = LMonadT $ do
    guardAlloc c
    setClearanceTCB c

-- Sets the current clearance to the join of the old clearance and the given clearance.
raiseClearanceTCB :: (Label l, LMonad m) => l -> LMonadT l m ()
raiseClearanceTCB c = LMonadT $ do
    (LState label clearance) <- get
    put $ LState label $ lub clearance c

-- Sets the current label to the meet of the old label and the given label.
lowerLabelTCB :: (Label l, LMonad m) => l -> LMonadT l m ()
lowerLabelTCB l = LMonadT $ do
    (LState label clearance) <- get
    put $ LState (glb label l) clearance

setCurrentLabelTCB :: (Label l, LMonad m) => l -> LMonadT l m ()
setCurrentLabelTCB l = do
    c <- getClearance
    LMonadT $ put $ LState l c

-- Labeled values.
data Labeled l a = Labeled {
        labeledLabel :: l
      , labeledValue :: a
    }

-- fullEraseLabel :: (Erasure l a, Label l) => l -> l -> a -> LMonadT l Maybe (ErasableD (Labeled l a))
-- fullEraseLabel l ll lv = do
--   eraseCheckPoint l
--   labeled <- label ll lv
--   let εlabeled = erase l labeled
--       -- Nothing??? or HOle??? does not type check
--   eraseCheckPoint l
--   return εlabeled




label :: (Label l, LMonad m) => l -> a -> LMonadT l m (Labeled l a)
label l a = LMonadT $ do
    guardAlloc l
    return $ Labeled l a

-- | Join the given label with the current label. 
-- Return the result if it can flow to the clearance.
taintHelper :: (Label l, LMonad m) => l -> LMonadT l m (Maybe l)
taintHelper l = do
    (LState label clearance) <- LMonadT get
    let l' = label `lub` l
    if l' `canFlowTo` clearance then
        return $ Just l'
    else
        return Nothing



-- -- runLMonad :: (Label l, LMonad m) => LMonadT l m a -> m a

-- eval :: (Label l) => l -> l -> LMonadT l Maybe a -> Maybe a
-- eval l cl ma =  (runLMonadWith l cl ma)


-- we can do similar things with free monad, but with foldFree to add
-- checkpoint at every single place
-- preErase :: (Label l, LMonad m)  => l -> LMonadT l m a -> LMonadT l m (Maybe a)
-- preErase l ma = do
--    -- lc <- getCurrentLabel
--    -- if lc `canFlowTo` l
--    -- then do a <- ma
--    --         return (Just a)
--    -- else return Nothing
--   -- eraseCheckPoint l
--   a <- ma
--   return (Just a)

-- postErase :: (Label l, LMonad m)  => l -> LMonadT l m a -> LMonadT l m (Maybe a)
-- postErase l ma = do
--    a <- ma
--    -- eraseCheckPoint l
--    return (Just a)
--    -- lc <- getCurrentLabel
--    -- if lc `canFlowTo` l
--    -- then return (Just a)
--    -- else return Nothing


-- add the axiom that erase is idempotent
-- {erase a == erase (erase a)}
-- class (Label l) => Erasure l a  where
--   type Erased l a
--   erase :: l -> a -> ErasableD (Erased l a)
  -- alternative
  -- erase :: l -> a -> Erased l a
  
  -- erase  :: a -> Erasable/Maybe a
  -- isHole :: a -> Bool



-- instance (Erasable (Maybe a)) where
--   erase _ = Nothing
--   isHole (Just _) = False
--   isHole Nothing = True

-- instance (not (Erasable l a) Label l) =>


-- instance (Erasure l a, Label l) => Erasure l ( (ErasableD (Labeled l a))) where
--   erase l la@(Labeled ll a) = if ll `canFlowTo` l then ErasableD (Labeled ll (erase l a)) else Hole
  -- join
  -- 
  
  -- isHole = undefined
  

-- inlined, fully erased unlabel

-- eraseCheckPoint :: (Label l) => l -> LMonadT l Maybe ()
-- eraseCheckPoint l = do
--   lc <- getCurrentLabel
--   lLift (guard $ lc `canFlowTo` l)
  
-- 

-- data ErasableD a = Hole | ErasableD a
--   deriving (Functor)

-- instance Monad ErasableD  where
--   return = ErasableD
--   m >>= f = join $ fmap f m
--     where
--       join (ErasableD (ErasableD a)) = ErasableD a
--       join _ = Hole

-- instance Applicative ErasableD where
--   pure = return
--   (<*>) = ap

-- fullEraseUnlabel :: (Erasure l a, Label l) => l -> Labeled l a -> LMonadT l Maybe a
-- fullEraseUnlabel l la@(Labeled ll lv) = do
--   -- corresponds to the smallstep transitive closure in the flexible dynamic ... paper
--   eraseCheckPoint l
--   let εla = (erase la)
--   v <- unlabel εla
--   eraseCheckPoint l
--   pure (erase v)
  -- where-- if ll `canFlowTo` l then Labeled ll lv
               -- else Labeled ll (erase lv) -- get into this branch => 
                    -- ll can't flow to l =>
                    -- lc `join` ll can't flow to l =>
                    -- will fail at checkPoint anyways =>
                    -- erasing Labeled is useless

-- postEraseUnlabel :: (Erasure l a, Label l) => l -> Labeled l a -> LMonadT l Maybe a
-- postEraseUnlabel l la = do
--   v <- unlabel la
--   checkPoint
--   pure $ erase v
--   where checkPoint = eraseCheckPoint l
        -- erase' a = do
        --   lc <- getCurrentLabel
        --   if lc `canFlowTo` l
        --     then erase a
        --     else 

{-@
unlabelPseudoSimulation :: (Erasable a, Label l)
=> l : l
-> lc : l
-> clc : l
-> la : Labeled l a
-> {eval lc clc (fullEraseUnlabel l la) == eval lc clc (postEraseUnlabel l la)}
@-}
-- unlabelPseudoSimulation :: (Erasure l a, Label l) =>
--   l -> l -> l -> Labeled l a -> Proof
-- unlabelPseudoSimulation l lc clc la = ()





-- {-@
-- unlabelNoninterference :: (label l)
-- => l : l
-- -> lc : l
-- -> lc' : l
-- -> clc : l
-- -> labeled : Labeled l a
-- -> ma : LMonadT l Identity a
-- -> ma' : LMonadT l Identity a
-- -> ((eval lc clc (preErase l (unlabel εlabeled))) ==  (eval lc' clc ?) ==>
--     (eval lc clc (postErase l ma)) == (eval lc clc (postErase l ma')))
-- @-}
-- unlabelNoninterference :: (Label l) =>
--   l -> Labeled l a -> LMonadT l Identity a -> LMonadT l Identity a -> Proof
-- unlabelNoninterference l Labeled{labeledLabel = vl, labeledValue = v} ma mb = ()
--   where εlabeled = if l `canFlowTo ` vl
--                    then Just Labeled {labeledLabel = vl, labeledValue = v}
--                    else Nothing



unlabel :: (Label l, LMonad m) => Labeled l a -> LMonadT l m a
unlabel l = do
    taintLabel $ labelOf l
    return $! labeledValue l

    -- setLabel $ labelOf l
    -- return $ labeledValue l



canUnlabel :: (Label l, LMonad m) => Labeled l a -> LMonadT l m Bool
canUnlabel l = do
    fmap (maybe False $ const True) $ taintHelper $ labelOf l

    -- clearance <- getClearance
    -- return $ canFlowTo (labelOf l) clearance

labelOf :: Label l => Labeled l a -> l
labelOf = labeledLabel

toLabeled :: (Label l, LMonad m, NFData a, MonadBaseControl IO m) => l -> LMonadT l m a -> LMonadT l m (Labeled l a)
toLabeled l ma = do
    LMonadT $ guardAlloc l

    oldLabel <- getCurrentLabel
    oldClearance <- getClearance

    a <- catchAnyDeep ma $ return . throw

    newLabel <- getCurrentLabel
    setCurrentLabelTCB oldLabel
    LMonadT $ setClearanceTCB oldClearance
    if newLabel `canFlowTo` l then
        return $ Labeled l a
    else
        LMonadT $ lift lFail

-- | Declassify a labeled value if the label joined with the current label can flow to the clearance. Does not raise the current label. 
-- Allows users to declassify the value if they have permission to read the value. 
declassifyTCB :: (Label l, LMonad m) => Labeled l a -> LMonadT l m a
declassifyTCB l@(Labeled _ v) = do
    canRead <- canUnlabel l
    if canRead then
        return v
    else
        LMonadT $ lift lFail

-- | Declassify a labeled value without any checks. 
declassifyNoChecksTCB :: (Label l, LMonad m) => Labeled l a -> LMonadT l m a
declassifyNoChecksTCB (Labeled _ v) = return v
        
swapBase :: (Label l, LMonad m, LMonad n) => (m (a,LState l) -> n (b,LState l)) -> LMonadT l m a -> LMonadT l n b
swapBase f (LMonadT m) = LMonadT $ do
    prev <- get
    ( res, new) <- lift $ f $ (runStateT m) prev
    put new
    return res


instance LMonad Maybe where
  lFail = Nothing
  lAllowLift = pure True


-- instance LMonad Identity where
--   lFail :: Identity a
--   lFail = pure undefined
