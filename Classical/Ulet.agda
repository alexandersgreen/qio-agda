module Ulet where

open import USem

open import Data.Nat
open import Data.Bool
open import Data.Vec hiding (init; last; _∷ʳ_)
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

UletU : ∀{n} -> (b : Bool) -> ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep {suc n} i u)) -> Vec Bool n -> Vec Bool n
UletU {n} b uq xs =  init (USem.f (proj₁ (uq (newQbit n))) (xs ∷ʳ b)) 

UletUR : ∀{n} -> (b : Bool) -> ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep {suc n} i u)) -> Vec Bool n -> Vec Bool n
UletUR {n} b uq xs =  init (USem.f⁻¹ (proj₁ (uq (newQbit n))) (xs ∷ʳ b)) 

!!∷ʳ : ∀{n} -> (xs : Vec Bool n) -> (b : Bool) -> (xs ∷ʳ b) !! newQbit n ≡ b
!!∷ʳ {zero} [] b = refl
!!∷ʳ {suc 0} (x ∷ []) b = refl
!!∷ʳ {suc (suc n)} (x ∷ x' ∷ xs) b = !!∷ʳ xs b

UletPhelper' : ∀{n} -> (u : USem (suc n)) -> (xs : Vec Bool n) -> (b : Bool) -> (last (USem.f u (xs ∷ʳ b)) ≡ b) -> (init (USem.f u (xs ∷ʳ b)) ∷ʳ b ≡ init (USem.f u (xs ∷ʳ b) ∷ʳ b))
UletPhelper' {n} u xs b p =  sym (initP {n} (USem.f u (xs ∷ʳ b)) b p ) 

UletUPhelper : ∀{n} -> (u : USem (suc n)) -> (xs : Vec Bool n) -> (b : Bool) -> (last (USem.f u (xs ∷ʳ b)) ≡ b) -> init (USem.f u (xs ∷ʳ b)) ∷ʳ b ≡ USem.f u (xs ∷ʳ b)
UletUPhelper {n} u xs b p = trans (UletPhelper' {n} u xs b p) (Pinit (USem.f u (xs ∷ʳ b)) ∷ʳ b) 

UletUPhelper'' : ∀{n} -> (u : USem (suc n)) -> (xs ys : Vec Bool (suc n)) -> xs ≡ ys -> init (USem.f⁻¹ u xs) ≡ init (USem.f⁻¹ u ys)
UletUPhelper'' {n} u xs ys p = funcP init (funcP (USem.f⁻¹ u) p)

lastH : ∀{n} -> {A : Set} -> (xs : Vec A (suc n)) -> last xs ≡ xs !! (newQbit n)
lastH (x ∷ []) = refl
lastH (x ∷ x' ∷ xs) = lastH (x' ∷ xs)

UletUP : ∀{n} -> (b : Bool) -> (uq : ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep {suc n} i u))) -> (xs : Vec Bool n) 
                      -> UletUR b uq (UletU b uq xs) ≡ xs
UletUP {n} b uq xs with proj₁ (uq (newQbit n)) | USem.p (proj₁ (uq (newQbit n))) {xs ∷ʳ b} | (Sep.s {suc n} {newQbit n} {(proj₁ (uq (newQbit n)))} ((proj₂ (uq (newQbit n))))) {xs ∷ʳ b} 
...| u | p  | p' = trans (UletUPhelper'' {n} 
                                         u 
                                         (init (USem.f u (xs ∷ʳ b)) ∷ʳ b) 
                                         (USem.f u (xs ∷ʳ b)) 
                                         (UletUPhelper {n} 
                                                       u 
                                                       xs 
                                                       b 
                                                       (trans 
                                                             (trans (lastH (USem.f u (xs ∷ʳ b)) ) 
                                                             p'
                                                       ) 
                                         (!!∷ʳ {n} xs b) ))
                         ) 
                         (trans (funcP init p) 
                                (Pinit xs ∷ʳ b)
                         )

UletPRhelper' : ∀{n} -> (u : USem (suc n)) -> (xs : Vec Bool n) -> (b : Bool) -> (last (USem.f⁻¹ u (xs ∷ʳ b)) ≡ b) -> (init (USem.f⁻¹ u (xs ∷ʳ b)) ∷ʳ b ≡ init (USem.f⁻¹ u (xs ∷ʳ b) ∷ʳ b))
UletPRhelper' {n} u xs b p =  sym (initP {n} (USem.f⁻¹ u (xs ∷ʳ b)) b p ) 

UletUPRhelper : ∀{n} -> (u : USem (suc n)) -> (xs : Vec Bool n) -> (b : Bool) -> (last (USem.f⁻¹ u (xs ∷ʳ b)) ≡ b) -> init (USem.f⁻¹ u (xs ∷ʳ b)) ∷ʳ b ≡ USem.f⁻¹ u (xs ∷ʳ b)
UletUPRhelper {n} u xs b p = trans (UletPRhelper' {n} u xs b p) (Pinit (USem.f⁻¹ u (xs ∷ʳ b)) ∷ʳ b) 

UletUPRhelper'' : ∀{n} -> (u : USem (suc n)) -> (xs ys : Vec Bool (suc n)) -> xs ≡ ys -> init (USem.f u xs) ≡ init (USem.f u ys)
UletUPRhelper'' {n} u xs ys p = funcP init (funcP (USem.f u) p)

UletUPR : ∀{n} -> (b : Bool) -> (uq : ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep {suc n} i u))) -> (xs : Vec Bool n) 
                      -> UletU b uq (UletUR b uq xs) ≡ xs
UletUPR {n} b uq xs with proj₁ (uq (newQbit n)) | USem.p⁻¹ (proj₁ (uq (newQbit n))) {xs ∷ʳ b} | (Sep.s⁻¹ {suc n} {newQbit n} {(proj₁ (uq (newQbit n)))} ((proj₂ (uq (newQbit n))))) {xs ∷ʳ b} 
...| u | p  | p' = trans (UletUPRhelper'' {n} 
                                          u 
                                          (init (USem.f⁻¹ u (xs ∷ʳ b)) ∷ʳ b) 
                                          (USem.f⁻¹ u (xs ∷ʳ b)) 
                                          (UletUPRhelper {n} 
                                                         u 
                                                         xs 
                                                         b 
                                                         (trans 
                                                               (trans (lastH (USem.f⁻¹ u (xs ∷ʳ b)) ) 
                                                               p'
                                                         ) 
                                           (!!∷ʳ {n} xs b) ))
                        ) 
                        (trans (funcP init p) 
                               (Pinit xs ∷ʳ b) 
                        )
 

Ulet : ∀{n : ℕ} -> (b : Bool) -> ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep {suc n} i u)) -> USem n -> USem n
Ulet {n} b uq u = record { f = \xs -> UletU b uq xs
                         ; f⁻¹ = \xs -> UletUR b uq xs 
                         ; p = \{xs} -> UletUP {n} b uq xs
                         ; p⁻¹ = \{xs} -> UletUPR {n} b uq xs
                         } ∙ u

