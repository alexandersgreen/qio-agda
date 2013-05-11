module Swap where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Insert functions and proofs
-------------------------------------------------------------------------------
insert : ∀{A n} -> A -> Vec A n -> (Qbit n) -> Vec A n
insert a [] ()
insert a (x ∷ xs) qzero = a ∷ xs
insert a (x ∷ xs) (qsuc i) = x ∷ (insert a xs i)

pinsert : ∀{n} -> (x : Bool) -> (xs : Vec Bool n) -> (i : Qbit n) -> (insert x xs i !! i) ≡ x
pinsert x [] ()
pinsert true (x ∷ xs) qzero = refl
pinsert false (x ∷ xs) qzero = refl
pinsert x (x' ∷ xs) (qsuc i) = pinsert x xs i

pinsert' : ∀{n} -> (x : Bool) -> (xs : Vec Bool n) -> (i : Qbit n) -> (insert (xs !! i) (insert x xs i) i) ≡ xs
pinsert' x [] ()
pinsert' x (x' ∷ xs) qzero = refl
pinsert' x (x' ∷ xs) (qsuc i) = cong (_∷_ x') (pinsert' x xs i) 

---------------------------------------------------------------------------------
-- Swap with function and proof (uses Insert functions and proofs)
---------------------------------------------------------------------------------
swapQ : ∀{n : ℕ} -> (Qbit n) -> (Qbit n) -> Vec Bool n -> Vec Bool n
swapQ qzero qzero (x ∷ xs) = x ∷ xs
swapQ qzero (qsuc i) (x ∷ xs) = insert x ((( x ∷ xs ) !! (qsuc i)) ∷ xs) (qsuc i)
swapQ (qsuc i) qzero (x ∷ xs) = insert x ((( x ∷ xs ) !! (qsuc i)) ∷ xs) (qsuc i)
swapQ (qsuc i) (qsuc i') (x ∷ xs) = x ∷ (swapQ i i' xs)

pswapQ : ∀{n : ℕ} -> (y y' : Qbit n) -> (x : Vec Bool n) -> swapQ y y' (swapQ y y' x) ≡ x
pswapQ () () []
pswapQ qzero qzero (x ∷ xs) = refl
pswapQ qzero (qsuc i) (x ∷ xs) = 2refl (pinsert x xs i) (pinsert' x xs i)
pswapQ (qsuc i) qzero (x ∷ xs) = 2refl (pinsert x xs i) (pinsert' x xs i)
pswapQ (qsuc i) (qsuc i') (x ∷ xs) = 2refl refl (pswapQ i i' xs)

Swap : ∀{n : ℕ} -> (Qbit n) -> (Qbit n) -> USem n -> USem n
Swap x y u = record { f = \xs -> swapQ x y xs 
                    ; f⁻¹ = \xs -> swapQ x y xs
                    ; p = \{xs} -> pswapQ x y xs
                    ; p⁻¹ = \{xs} -> pswapQ x y xs
                    } ∙ u
---------------------------------------------------------------------------------