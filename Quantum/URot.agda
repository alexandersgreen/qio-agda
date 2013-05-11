module URot where

open import USem
open import Data.Nat
open import Data.Bool
open import Data.Vec hiding (map)
open import Data.List
open import Data.Product hiding (map)
open import Relation.Binary.Core
open import Complex
open import ListOps renaming (map to map')
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- URot with function and proof
------------------------------------------------------------------------------
_∷'_ : ∀{n} -> Bool -> Base n -> Base (suc n)
b ∷' (bs ∘ c) = (b ∷ bs) ∘ c

rotate : ∀{n} -> (Qbit n) -> Rotation -> Base n -> List (Base n)
rotate qzero 
       (Rotate (r , p))
       ((false ∷ xs) ∘ c)
       = ((false ∷ xs)) ∘ (Rot.a r ×ℂ c) ∷ ((true ∷ xs)) ∘ (Rot.b r ×ℂ c) ∷ []
rotate qzero 
       (Rotate (r , p))
       ((true ∷ xs) ∘ c)
       = (false ∷ xs) ∘ (Rot.c r ×ℂ c) ∷ (true ∷ xs) ∘ (Rot.d r ×ℂ c) ∷ []
rotate (qsuc i) r ((x ∷ xs) ∘ c) = map (\xs' -> x ∷' xs') (rotate i r (xs ∘ c))


rotateP : ∀{n} -> (q : Qbit n) -> (r : Rotation) -> (xs : Base n) -> join (map (rotate q (r *')) (rotate q r xs)) ≡S xs
rotateP {zero} () r xs
rotateP {suc n} qzero (Rotate (r , p)) ((true ∷ xs) ∘ c) = record { xs' = (true ∷ xs) ∘ (conjugate (Rot.c r) ×ℂ (Rot.c r ×ℂ c)) ∷ (true ∷ xs) ∘ (conjugate (Rot.d r) ×ℂ (Rot.d r ×ℂ c)) ∷ []
                                                          ; p = trans (removeZero silly) (cong (\x -> ((true ∷ xs) ∘ (conjugate (Rot.c r) ×ℂ (Rot.c r ×ℂ c))) ∷ x) (removeZero silly))
                                                          ; bs = refl
                                                          ; cs = silly
                                                          }
rotateP {suc n} qzero (Rotate (r , p)) ((false ∷ xs) ∘ c) = record { xs' = _
                                                           ; p = refl
                                                           ; bs = silly
                                                           ; cs = silly
                                                           }
rotateP {suc n} (qsuc i) r ((x ∷ xs) ∘ c) = record { xs' = _
                                            ; p = refl
                                            ; bs = silly
                                            ; cs = silly
                                            }

URot : ∀{n : ℕ} -> (Qbit n) -> Rotation -> USem n -> USem n
URot {n} q r u = record { f =  rotate q r 
                        ; f⁻¹ =  rotate q (r *') 
                        ; p = \{xs} -> rotateP q r xs
                        ; p⁻¹ = \{xs} -> record { xs' = _
                                                ; p = refl
                                                ; bs = silly
                                                ; cs = silly
                                                }
                        } ∙ u