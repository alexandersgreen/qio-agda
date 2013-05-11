module Cond where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec hiding (map)
open import Data.List
open import Relation.Binary.Core
open import Data.Product hiding (map)
open import Complex
open import ListOps renaming (map to map')

----------------------------------------------------------------------------------
--Cond with functions and proofs
----------------------------------------------------------------------------------
condQ : ∀{n} -> (i : Qbit n) -> (fb : (Bool -> (Σ (USem n) (\u -> Sep i u)))) -> (x : Base n) -> List (Base n)
condQ i fb x = USem.f (proj₁ (fb (lookupQ i x))) x

condQR : ∀{n} -> (i : Qbit n) -> (fb : (Bool -> (Σ (USem n) (\u -> Sep i u)))) -> (x : Base n) -> List (Base n)
condQR i fb x = USem.f⁻¹ (proj₁ (fb (lookupQ i x))) x

Cond : ∀{n : ℕ} -> (i : Qbit n) -> (Bool -> (Σ (USem n) (\u -> Sep i u))) -> USem n -> USem n
Cond {n} q fb u = record { f =  condQ q fb
                         ; f⁻¹ = condQR q fb   
                         ; p =  \{xs} -> record { xs' = _
                                                ; p = refl
                                                ; bs = silly
                                                ; cs = silly
                                                }     
                         ; p⁻¹ = \{xs} -> record { xs' = _
                                                 ; p = refl 
                                                 ; bs = silly
                                                 ; cs = silly
                                                 }   
                         } ∙ u

