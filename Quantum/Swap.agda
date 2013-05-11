module Swap where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec hiding (_++_; [_]; map)
open import Data.List
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Complex
open import ListOps renaming (map to map')

------------------------------------------------------------------------------
-- Insert functions and proofs
-------------------------------------------------------------------------------
insert' : {A : Set} -> ∀{n} -> A -> Vec A n -> Qbit n -> Vec A n 
insert' a [] ()
insert' a (x ∷ xs) qzero = a ∷ xs
insert' a (x ∷ xs) (qsuc i) = x ∷ (insert' a xs i)

insert : ∀{n} -> Bool -> Base n -> Qbit n -> Base n
insert b (bs ∘ c) q = (insert' b bs q) ∘ c

pinsert' : ∀{n} -> (x : Bool) -> (xs : Vec Bool n) -> (i : Qbit n) -> (insert' x xs i !! i) ≡ x
pinsert' x [] ()
pinsert' true (x ∷ xs) qzero = refl
pinsert' false (x ∷ xs) qzero = refl
pinsert' x (x' ∷ xs) (qsuc i) = pinsert' x xs i

pinsert : ∀{n } -> (x : Bool) -> (xs : Base n) -> (i : Qbit n) -> (lookupQ i (insert x xs i)) ≡ x
pinsert {n} b (bs ∘ c) q = trans (sym (!!P {n} {insert' b bs q} {c} {q} {b})) (pinsert' b bs q)


pinserti' : ∀{n} -> (x : Bool) -> (xs : Vec Bool n) -> (i : Qbit n) -> (insert' (xs !! i) (insert' x xs i) i) ≡ xs
pinserti' x [] ()
pinserti' x (x' ∷ xs) qzero = refl
pinserti' x (x' ∷ xs) (qsuc i) = 2refl refl (pinserti' x xs i)

pinserti : ∀{n} -> (x : Bool) -> (xs : Base n) -> (i : Qbit n) -> insert ((lookupQ i xs)) (insert x xs i) i ≡ xs 
pinserti {n} b (bs ∘ c) q = baseP (trans (funcP (\b' -> insert' b' (insert' b bs q) q) (sym (!!P {n} {bs} {c} {q} {b}))) (pinserti' b bs q)) refl


---------------------------------------------------------------------------------
-- Swap with function and proof (uses Insert functions and proofs)
---------------------------------------------------------------------------------
swapQ' : ∀{n : ℕ} -> (Qbit n) -> (Qbit n) -> Vec Bool n -> Vec Bool n
swapQ' qzero qzero (x ∷ xs) = x ∷ xs
swapQ' qzero (qsuc i) (x ∷ xs) = insert' x ((( x ∷ xs ) !! (qsuc i)) ∷ xs) (qsuc i)
swapQ' (qsuc i) qzero (x ∷ xs) = insert' x ((( x ∷ xs ) !! (qsuc i)) ∷ xs) (qsuc i)
swapQ' (qsuc i) (qsuc i') (x ∷ xs) = x ∷ (swapQ' i i' xs)

swapQ : ∀{n} -> Qbit n -> Qbit n -> Base n -> List (Base n)
swapQ q1 q2 (bs ∘ c) = [ (swapQ' q1 q2 bs ∘ c) ]

pswapQ' : ∀{n : ℕ} -> (y y' : Qbit n) -> (x : Vec Bool n) -> swapQ' y y' (swapQ' y y' x) ≡ x
pswapQ' () () []
pswapQ' qzero qzero (x ∷ xs) = refl
pswapQ' qzero (qsuc i) (x ∷ xs) = 2refl (pinsert' x xs i) (pinserti' x xs i)
pswapQ' (qsuc i) qzero (x ∷ xs) = 2refl (pinsert' x xs i) (pinserti' x xs i)
pswapQ' (qsuc i) (qsuc i') (x ∷ xs) = 2refl refl (pswapQ' i i' xs)

pswapQ : ∀{n} -> (x y : Qbit n) -> (xs : Base n) -> join (map (swapQ x y) (swapQ x y xs)) ≡S xs
pswapQ x y (y' ∘ y0) = record { xs' = _
                              ; p = refl
                              ; bs = cong (\x -> x ∷ []) (pswapQ' x y y')
                              ; cs = zero+ℂ
                              }

Swap : ∀{n : ℕ} -> (Qbit n) -> (Qbit n) -> USem n -> USem n
Swap x y u = record { f = \xs -> swapQ x y xs 
                    ; f⁻¹ = \xs -> swapQ x y xs 
                    ; p =  \{xs} -> pswapQ x y xs     
                    ; p⁻¹ =  \{xs} -> pswapQ x y xs   
                    } ∙ u
---------------------------------------------------------------------------------