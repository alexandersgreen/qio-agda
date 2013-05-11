module USem where

open import Data.Vec hiding (reverse; _++_; init; _∷ʳ_; last)
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Relation.Binary.Core
open import Data.Unit
open import Algebra
open import Relation.Binary.PropositionalEquality
open import Algebra.Structures

data Qbit : ℕ -> Set where
  qzero : {n : ℕ} → Qbit (suc n)
  qsuc  : {n : ℕ} (i : Qbit n) → Qbit (suc n)

newQbit : (n : ℕ) -> Qbit (suc n)
newQbit zero = qzero
newQbit (suc n) = qsuc (newQbit n)

_!!_ : ∀{A n} -> Vec A n -> (Qbit n) -> A
[] !! ()
(x ∷ xs) !! qzero = x
(x ∷ xs) !! qsuc i = xs !! i

record USem (n : ℕ) : Set where
  field
   f   : Vec Bool n -> Vec Bool n 
   f⁻¹ : Vec Bool n -> Vec Bool n
   p : ∀{x : Vec Bool n} -> f⁻¹ (f x) ≡ x
   p⁻¹ : ∀{x : Vec Bool n} -> f (f⁻¹ x) ≡ x

2refl : ∀{n : ℕ} -> ∀{A : Set} -> {x x' : A} -> {xs xs' : Vec A n} -> (x ≡ x') -> (xs ≡ xs') -> (x ∷ xs) ≡ (x' ∷ xs')
2refl refl refl = refl

funcP : ∀{A B : Set} -> {a b : A} -> (f : A -> B) -> a ≡ b -> f a ≡ f b
funcP f refl = refl

combineP : ∀{n : ℕ} -> {xs : Vec Bool n} -> (u : USem n) -> (u' : USem n) -> USem.f⁻¹ u (USem.f⁻¹ u' (USem.f u' (USem.f u xs))) ≡ xs
combineP {n} {xs} u u' with USem.p u {xs} | funcP (USem.f⁻¹ u) ((USem.p u') {(USem.f u) xs})
...| a | b = trans b a

combinePR : ∀{n : ℕ} -> {xs : Vec Bool n} -> (u : USem n) -> (u' : USem n) -> USem.f u' (USem.f u (USem.f⁻¹ u (USem.f⁻¹ u' xs))) ≡ xs
combinePR {n} {xs} u u' with USem.p⁻¹ u' {xs} | funcP (USem.f u') ((USem.p⁻¹ u) {(USem.f⁻¹ u') xs})
...| a | b = trans b a

mempty : ∀{n} -> USem n
mempty = record { f = \x -> x 
                ; f⁻¹ = \x -> x
                ; p = refl
                ; p⁻¹ = refl
                }

mappend : ∀{n} -> (USem n) -> (USem n) -> (USem n)
mappend u u' = record { f = \xs -> (USem.f u') ((USem.f u) xs) 
                      ; f⁻¹ = \xs -> (USem.f⁻¹ u) ((USem.f⁻¹ u') xs)
                      ; p = combineP u u'
                      ; p⁻¹ = combinePR u u'
                      }

record _U_ {n : ℕ} (r r' : USem n) : Set where
  field
    p : USem.f r ≡ USem.f r'
    p⁻¹ : USem.f⁻¹ r ≡ USem.f⁻¹ r' 

isEquivalence≡USem≡ : ∀{n} -> IsEquivalence (_U_ {n})
isEquivalence≡USem≡ = record { refl = record { p = refl
                                              ; p⁻¹ = refl
                                              }
                             ; trans = \p p' -> record { p = trans (_U_.p p) (_U_.p p')
                                                       ; p⁻¹ = trans (_U_.p⁻¹ p) (_U_.p⁻¹ p')
                                                       }
                             ; sym = \p -> record { p = sym (_U_.p p)
                                                  ; p⁻¹ = sym (_U_.p⁻¹ p)
                                                  }
                             }
assocMappend : ∀{n} -> (x y z : USem n) -> mappend (mappend x y) z U mappend x (mappend y z)
assocMappend x y z = record { p = refl
                            ; p⁻¹ = refl
                            }

mappend-pres-U : ∀{n} -> {x y u v : USem n} -> x U y → u U v → mappend x u U mappend y v
mappend-pres-U {n} {x} {y} {u} {v} xy uv = record { p = trans (cong (\u' x' -> (USem.f u (u' x'))) (_U_.p xy)) 
                                                              (cong (\u' x' -> u' (USem.f y x')) (_U_.p uv))
                                                  ; p⁻¹ = trans (cong (\u' x' -> (USem.f⁻¹ x (u' x'))) (_U_.p⁻¹ uv)) 
                                                                (cong (\u' x' -> u' (USem.f⁻¹ v x')) (_U_.p⁻¹ xy))
                                                  }


isSemiGroupUSem : ∀{n} -> IsSemigroup (_U_ {n}) mappend
isSemiGroupUSem = record { isEquivalence = isEquivalence≡USem≡
                         ; assoc = assocMappend
                         ; ∙-pres-≈ = mappend-pres-U
                         }

usemLID : ∀{n} -> (x : USem n) -> mappend mempty x U x
usemLID x = record { p = refl
                   ; p⁻¹ = refl
                   }

usemRID : ∀{n} -> (x : USem n) -> mappend x mempty U x
usemRID x = record { p = refl
                   ; p⁻¹ = refl
                   }


isMonoidUSem : ∀{n} -> IsMonoid (_U_ {n}) mappend mempty
isMonoidUSem = record { isSemigroup = isSemiGroupUSem
                      ; identity = usemLID , usemRID
                      }


monoidUSem : ∀{n} -> Monoid
monoidUSem {n} = record { carrier = USem n
                        ; _≈_ = _U_
                        ; _∙_ = mappend 
                        ; ε = mempty
                        ; isMonoid = isMonoidUSem
                        }

open module mU {n} = Monoid (monoidUSem {n}) public hiding (refl; trans; sym)


reverse : ∀{n} -> USem n -> USem n
reverse u = record { f = USem.f⁻¹ u
                   ; f⁻¹ = USem.f u
                   ; p = USem.p⁻¹ u
                   ; p⁻¹ = USem.p u
                   }

init : ∀{n} -> {A : Set} -> Vec A (suc n) -> Vec A n
init (x ∷ []) = []
init (x ∷ x' ∷ xs) = x ∷ init (x' ∷ xs)

last : ∀{n} -> {A : Set} -> Vec A (suc n) -> A
last (x ∷ []) = x
last (x ∷ x' ∷ xs) = last (x' ∷ xs)

_∷ʳ_ : ∀{n} -> {A : Set} -> Vec A n -> A -> Vec A (suc n)
[] ∷ʳ x = [ x ]
(x ∷ xs) ∷ʳ x' = x ∷ (xs ∷ʳ x')

initP :  ∀{n} -> {A : Set} -> (xs : Vec A (suc n)) -> (x : A) -> (last xs ≡ x) -> init (xs ∷ʳ x) ≡ (init xs) ∷ʳ x
initP (x ∷ []) x' p = funcP (\x -> x ∷ []) p
initP (x ∷ x' ∷ xs) x'' p = funcP (_∷_ x) (initP (x' ∷ xs) x'' p)

Pinit_∷ʳ_ : ∀{n} -> {A : Set} -> (xs : Vec A n) -> (x : A) -> init (xs ∷ʳ x) ≡ xs
Pinit [] ∷ʳ x = refl
Pinit x ∷ [] ∷ʳ x' = refl
Pinit x ∷ x' ∷ xs ∷ʳ x0 = funcP (_∷_ x) ((Pinit x' ∷ xs ∷ʳ x0))

headtail : ∀{n A}  -> {xs : Vec A (suc n)} -> head xs ∷ tail xs ≡ xs
headtail {n} {A} {x ∷ xs} = refl

liftU : ∀{n} -> USem n -> USem (suc n)
liftU u = record { f = \xs -> head xs ∷ USem.f u (tail xs) 
                 ; f⁻¹ = \xs -> head xs ∷ USem.f⁻¹ u (tail xs)
                 ; p = \{xs} -> trans (funcP (_∷_ (head xs)) (USem.p u {tail xs})) headtail 
                 ; p⁻¹ = \{xs} -> trans (funcP (_∷_ (head xs)) (USem.p⁻¹ u {tail xs})) headtail
                 }


---------------------------------------------------------------------------------
-- Sep data-type - defines seperability requirement
---------------------------------------------------------------------------------

record Sep {n : ℕ} (i : Qbit n) (u : USem n) : Set where
  field
    s : ∀{xs} -> ((USem.f u xs) !! i ≡ xs !! i)
    s⁻¹ : ∀{xs} -> ((USem.f⁻¹ u xs) !! i ≡ xs !! i)
 

----------------------------------------------------------------------------------