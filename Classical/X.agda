module X where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- X with Negate function and proof
------------------------------------------------------------------------------
negate : ∀{n : ℕ} -> (Qbit n) -> Vec Bool n -> Vec Bool n
negate () []
negate qzero (x ∷ xs) = (not x) ∷ xs
negate (qsuc i) (x ∷ xs) = x ∷ (negate i xs)

pnegate : ∀{n : ℕ} -> (x : Vec Bool n) -> (y : Qbit n) -> negate y (negate y x) ≡ x
pnegate [] ()
pnegate (true ∷ xs) qzero = refl
pnegate (false ∷ xs) qzero = refl
pnegate (x ∷ xs) (qsuc i) = cong (_∷_ x) (pnegate xs i)

X : ∀{n : ℕ} -> (Qbit n) -> USem n -> USem n
X q u = record { f = \xs -> negate q xs
               ; f⁻¹ = \xs -> negate q xs
               ; p = \{xs} -> pnegate xs q 
               ; p⁻¹ = \{xs} -> pnegate xs q
               } ∙ u