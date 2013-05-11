module ListOps where

open import Data.Vec hiding (map; _++_; [_]) renaming (_∷_ to _∷'_)
open import Data.List hiding (map) renaming (_++_ to _+++_)
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Relation.Binary.Core
open import Data.Product hiding (map)
open import Complex

data Qbit : ℕ -> Set where
  qzero : {n : ℕ} → Qbit (suc n)
  qsuc  : {n : ℕ} (i : Qbit n) → Qbit (suc n)

data Base (n : ℕ) : Set where
  _∘_ : Vec Bool n -> ℂ -> Base n

postulate
  removeZero : ∀{n} -> {x : Vec Bool n} -> {c : ℂ} -> {xs : List (Base n)} -> (c ≡ zeroℂ) -> (x ∘ c) ∷ xs ≡ xs


emptyBase : Base (zero)
emptyBase = [] ∘ oneℂ

_==_ : ∀{n} -> Vec Bool n -> Vec Bool n -> Bool
[] == [] = true
(x ∷' xs) == (x' ∷' xs') = (not (x xor x')) ∧ xs == xs'

2refl : ∀{n : ℕ} -> ∀{A : Set} -> {x x' : A} -> {xs xs' : Vec A n} -> (x ≡ x') -> (xs ≡ xs') -> _≡_ {Vec A (suc n)} (x ∷' xs) (x' ∷' xs')
2refl refl refl = refl

funcP : ∀{A B : Set} -> {a b : A} -> (f : A -> B) -> a ≡ b -> f a ≡ f b
funcP f refl = refl

_!!_ : {A : Set} -> ∀{n :  ℕ} -> Vec A n -> (Qbit n) -> A
[] !! ()
(x ∷' xs) !! qzero = x
(x ∷' xs) !! qsuc i = xs !! i

lookupQ : ∀{n : ℕ} -> (Qbit n) -> Base n -> Bool
lookupQ qzero ((x ∷' xs) ∘ c) = x 
lookupQ (qsuc i) ((x ∷' xs) ∘ c) = lookupQ i (xs ∘ c)

!!P : ∀{n} -> {xs : Vec Bool n} -> {c : ℂ} -> {q : Qbit n} -> {b : Bool} -> (xs !! q ≡  (lookupQ q (xs ∘ c)))
!!P {zero} {xs} {c} {()} {b}
!!P {suc n} {x ∷' xs} {c} {qzero} {b} =  refl 
!!P {(suc n)} {x ∷' xs} {c} {qsuc i} {b} =  !!P {n} {xs} {c} {i} {b}

_∷≡_ : {A : Set} -> {a b : A} -> {as bs : List A} -> (a ≡ b) -> (as ≡ bs) -> _≡_ {List A} (a ∷ as) (b ∷ bs)
refl ∷≡ refl = refl 

baseP : ∀{n} -> {as bs : Vec Bool n} -> {c d : ℂ} -> (as ≡ bs) -> (c ≡ d) -> as ∘ c ≡ bs ∘ d
baseP refl refl = refl

_∷∷_ : ∀{n} -> Base n -> List (Base n) -> List (Base n) 
(b ∘ c) ∷∷ [] = [ b ∘ c ]
(b ∘ c) ∷∷ (b' ∘ c' ∷ bcs) with b == b'
...| true = ((b ∘ (c +ℂ c')) ∷ bcs)
...| false = ((b' ∘ c') ∷ (b ∘ c) ∷∷ bcs)


_++_ : ∀{n} -> List (Base n) -> List (Base n) -> List (Base n)
bs ++ [] = bs
bs ++ (b ∷ bs') =  (b ∷∷ bs) ++ bs' 
 
map : ∀{n} -> (Base n -> List (Base n)) -> List (Base n) -> List (Base n)
map f [] = []
map f (x ∷ xs) = f x ++ map f xs
