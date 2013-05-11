module Cond where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Relation.Binary.Core
open import Data.Product
open import Relation.Binary.PropositionalEquality

----------------------------------------------------------------------------------
--Cond with functions and proofs
----------------------------------------------------------------------------------
condQ : ∀{n} -> (i : Qbit n) -> (Bool -> (Σ (USem n) (\u -> Sep {n} i u))) -> Vec Bool n -> Vec Bool n
condQ i fb xs = USem.f (proj₁ (fb (xs !! i))) xs

condQR : ∀{n} -> (i : Qbit n) -> (Bool -> (Σ (USem n) (\u -> Sep {n} i u))) -> Vec Bool n -> Vec Bool n
condQR i fb xs = USem.f⁻¹ (proj₁ (fb (xs !! i))) xs

condQPhelper : ∀{n} -> {s t : USem n} -> {xs : Vec Bool n} -> (s ≡ t) 
                    -> USem.f⁻¹ t (USem.f s xs) ≡ USem.f⁻¹ s (USem.f s xs)
condQPhelper refl = refl

condQP : ∀{n} -> {xs : Vec Bool n} -> (i : Qbit n) 
              -> ( fb : (Bool -> (Σ (USem n) (\u -> Sep {n} i u)))) 
              -> condQR i fb (condQ i fb xs) ≡ xs
condQP {n} {xs} i fb = trans (condQPhelper {n} 
                                           {proj₁ (fb (xs !! i))} 
                                           {proj₁ (fb (USem.f (proj₁ (fb (xs !! i))) xs !! i))} 
                                           {xs} 
                                           (funcP (\b -> proj₁ (fb b)) (sym ( Sep.s (proj₂ (fb (xs !! i))) ) ))
                             ) 
                             (USem.p (proj₁ (fb (xs !! i))) {xs})

  
condQPRhelper : ∀{n} -> {s t : USem n} -> {xs : Vec Bool n} -> (s ≡ t) 
                     -> USem.f t (USem.f⁻¹ s xs) ≡ USem.f s (USem.f⁻¹ s xs)
condQPRhelper refl = refl

condQPR : ∀{n} -> {xs : Vec Bool n} -> (i : Qbit n) 
               -> (fb : (Bool -> (Σ (USem n) (\u -> Sep {n} i u)))) 
               -> condQ i fb (condQR i fb xs) ≡ xs
condQPR {n} {xs} i fb = trans (condQPRhelper {n} 
                                             {proj₁ (fb (xs !! i))} 
                                             {proj₁ (fb (USem.f⁻¹ (proj₁ (fb (xs !! i))) xs !! i))} 
                                             {xs} 
                                             (funcP (\b -> proj₁ (fb b)) (sym ( Sep.s⁻¹ (proj₂ (fb (xs !! i))) )))
                               ) 
                               (USem.p⁻¹ (proj₁ (fb (xs !! i))) {xs})



Cond : ∀{n : ℕ} -> (i : Qbit n) -> (Bool -> (Σ (USem n) (\u -> Sep {n} i u))) -> USem n -> USem n
Cond {n} q fb u = record { f = \xs -> condQ q fb xs
                         ; f⁻¹ = \xs -> condQR q fb xs
                         ; p =  \{xs} ->   condQP {n} {xs} q fb 
                         ; p⁻¹ = \{xs} ->   condQPR {n} {xs} q fb 
                         } ∙ u

