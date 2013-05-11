module Ulet where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec hiding (init; last; _∷ʳ_; _∷ʳ'_; [_]; map)
open import Data.List
open import Data.Product hiding (map)
open import Relation.Binary.Core
open import Complex
open import ListOps renaming (map to map')

init' : ∀{n} -> {A : Set} -> Vec A (suc n) -> Vec A n
init' (x ∷ []) = []
init' (x ∷ x' ∷ xs) = x ∷ init' (x' ∷ xs)

init : ∀{n} -> Base (suc n) -> Base n
init (bs ∘ c) = (init' bs) ∘ c

last : ∀{n} -> {A : Set} -> Vec A (suc n) -> A
last (x ∷ []) = x
last (x ∷ x' ∷ xs) = last (x' ∷ xs)

_∷ʳ_ : ∀{n} -> {A : Set} -> Vec A n -> A -> Vec A (suc n)
[] ∷ʳ x = x ∷ []
(x ∷ xs) ∷ʳ x' = x ∷ (xs ∷ʳ x')

_∷ʳ'_ : ∀{n} -> Base n -> Bool -> Base (suc n)
(bs ∘ c) ∷ʳ' b = (bs ∷ʳ b) ∘ c

initP :  ∀{n} -> {A : Set} -> (xs : Vec A (suc n)) -> (x : A) -> (last xs ≡ x) -> init' (xs ∷ʳ x) ≡ (init' xs) ∷ʳ x
initP (x ∷ []) x' p = funcP (\x -> x ∷ []) p
initP (x ∷ x' ∷ xs) x'' p = funcP (_∷_ x) (initP (x' ∷ xs) x'' p)

Pinit_∷ʳ_ : ∀{n} -> {A : Set} -> (xs : Vec A n) -> (x : A) -> init' (xs ∷ʳ x) ≡ xs
Pinit [] ∷ʳ x = refl
Pinit x ∷ [] ∷ʳ x' = refl
Pinit x ∷ x' ∷ xs ∷ʳ x0 = funcP (_∷_ x) ((Pinit x' ∷ xs ∷ʳ x0))   

UletU : ∀{n} -> (b : Bool) -> (uq : (i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep i u)) -> Base n -> List (Base n)
UletU {n} b uq (y ∘ c) = map init (USem.f (proj₁ (uq (newQbit n))) ((y ∷ʳ b) ∘ c)) 

UletUR : ∀{n} -> (b : Bool) -> (uq : (i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep i u)) -> Base n -> List (Base n)
UletUR {n} b uq (y ∘ c) = map init (USem.f⁻¹ (proj₁ (uq (newQbit n))) ((y ∷ʳ b) ∘ c))

!!∷ʳ : ∀{n} -> (xs : Vec Bool n) -> (b : Bool) -> (xs ∷ʳ b) !! newQbit n ≡ b
!!∷ʳ {zero} [] b = refl
!!∷ʳ {suc 0} (x ∷ []) b = refl
!!∷ʳ {suc (suc n)} (x ∷ x' ∷ xs) b = !!∷ʳ xs b

lastH : ∀{n} -> {A : Set} -> (xs : Vec A (suc n)) -> last xs ≡ xs !! (newQbit n)
lastH (x ∷ []) = refl
lastH (x ∷ x' ∷ xs) = lastH (x' ∷ xs)

Ulet : ∀{n : ℕ} -> (b : Bool) -> ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep i u)) -> USem n -> USem n
Ulet {n} b uq u = record { f = UletU b uq
                         ; f⁻¹ = UletUR b uq 
                         ; p = \{xs} -> record { xs' = _
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

