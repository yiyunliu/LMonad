{-@ LIQUID "--reflection" @-}
module LMonad.Label where

import Prelude
import ProofCombinators

{-@ class measure canFlowTo :: forall l . l -> l -> Bool @-}
{-@ class measure lub :: forall l . l -> l -> l @-}
{-@ class measure glb :: forall l . l -> l -> l @-}
{-@ class measure bot :: forall l . l @-}
{-@ class Label l where
      canFlowTo :: a : l -> b : l -> {v : Bool | v == canFlowTo a b}
      glb :: a : l -> b : l -> {v : l | v == glb a b}
      lub :: a : l -> b : l -> {v : l | v == lub a b}
      bot  :: {v:l | v == bot } 

      lawFlowReflexivity :: l : l -> {v : () | canFlowTo l l}
      lawFlowAntisymmetry :: a : l -> {b : l | canFlowTo a b && canFlowTo b a} -> {v : () | a == b}
      lawFlowTransitivity :: a:l -> b:l-> c:l -> {(canFlowTo a b && canFlowTo b c) => canFlowTo a c}

      lawGlb :: z : l -> x : l -> y : l -> w : l -> {z == glb x y => (canFlowTo z x && canFlowTo z y && ((canFlowTo w x && canFlowTo w y) => canFlowTo w z))}
      lawLub :: z : l -> x : l -> y : l -> w : l -> {z == lub x y => (canFlowTo x z && canFlowTo y z && ((canFlowTo x w && canFlowTo y w) => canFlowTo z w))}
      lawBot  :: x : l -> { canFlowTo bot x }
@-}

class Label l where

    canFlowTo :: l -> l -> Bool

    -- Lub
    lub :: l -> l -> l
    -- Glb
    glb :: l -> l -> l


    bottom :: l

  
    lawFlowReflexivity :: l -> Proof
    lawFlowAntisymmetry :: l -> l -> Proof
    lawFlowTransitivity :: l -> l -> l -> Proof
    
    lawGlb :: l -> l -> l -> l -> Proof
    lawLub :: l -> l -> l -> l -> Proof
    lawBot  :: l -> Proof



{-@ lubCanFlowTo 
 :: Label l
 => l1 : l
 -> l2 : l
 -> l3 : l
 -> {canFlowTo l1 l3 && canFlowTo l2 l3 <=> canFlowTo (lub l1 l2) l3}
 @-}
lubCanFlowTo :: Label l => l -> l -> l -> ()
lubCanFlowTo l1 l2 l3 = lawLub (lub l1 l2) l1 l2 l3 &&& unlubCanFlowTo l1 l2 l3 


{-@ unlubCanFlowTo 
 :: Label l
 => l1:l -> l2:l -> l3:l 
 -> {canFlowTo (lub l1 l2) l3 => (canFlowTo l1 l3  && canFlowTo l2 l3)}
 @-}
unlubCanFlowTo :: Label l => l -> l -> l -> ()
unlubCanFlowTo l1 l2 l3 
  =     lawLub (lub l1 l2) l1 l2 l3  
    &&& lawFlowTransitivity l1 (l1 `lub` l2) l3 
    &&& lawFlowTransitivity l2 (l1 `lub` l2) l3 

{-@ notLubCanFlowTo 
 :: Label l 
 => a : l 
 -> b : l 
 -> c : {l | not (canFlowTo a c)}
 -> {not (canFlowTo (lub a b) c)}
 @-}
notLubCanFlowTo :: Label l => l -> l -> l -> ()
notLubCanFlowTo l1 l2 l3 = unlubCanFlowTo l1 l2 l3

{-@ notCanFlowTo 
 :: Label l 
 => a : l 
 -> b : l 
 -> c : l
 -> {not (canFlowTo b a) && canFlowTo b c => not (canFlowTo c a)}
 @-}
notCanFlowTo :: Label l => l -> l -> l -> ()
notCanFlowTo a b c 
  | b `canFlowTo` c 
  = lawFlowTransitivity b c a  
notCanFlowTo a b c 
  = ()

unlubCanFlowToItself :: Label l => l -> l -> ()
{-@ unlubCanFlowToItself :: Label l => a:l -> b:l 
  -> { canFlowTo a (lub a b) && canFlowTo b (lub a b) } @-}
unlubCanFlowToItself x y = lawLub (x `lub` y) x y x   
 
