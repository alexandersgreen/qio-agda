module USem where

open import Data.Vec hiding (reverse; sum; _++_; map; foldr; [_])
open import Data.List hiding (reverse; sum; monoid)
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Complex
open import ListOps renaming (map to map'; _++_ to _+++_)
open import Algebra


newQbit : (n : ℕ) -> Qbit (suc n)
newQbit zero = qzero
newQbit (suc n) = qsuc (newQbit n)

repeat : ∀{A} -> A -> (n : ℕ) -> List A
repeat x zero = []
repeat x (suc n) = x ∷ repeat x n

join : ∀{A} -> List (List A) -> List A
join [] = []
join (x ∷ xs) = x ++ join xs

extractℂ : ∀{n} -> Base n -> ℂ
extractℂ (y ∘ y') = y'

extractVecBool : ∀{n} -> Base n -> Vec Bool n
extractVecBool (y ∘ y') = y 

record _≡S_ {n : ℕ} (xs : List (Base n)) (x : Base n) : Set where
  field
    xs' : List (Base n)
    p : xs ≡ xs'
    bs : map (extractVecBool) xs' ≡ map (extractVecBool) (repeat x (length xs')) 
    cs : foldr _+ℂ_  zeroℂ (map extractℂ xs') ≡ extractℂ x

record USem (n : ℕ) : Set where
  field
   f :  Base n -> List (Base n)
   f⁻¹ : Base n -> List (Base n)
   p : {x : Base n} -> (join (map f⁻¹ (f x))) ≡S x
   p⁻¹ : {x : Base n} -> (join (map f (f⁻¹ x))) ≡S x



mempty : ∀{n} ->  USem n
mempty {n} = record { f = \x -> [ x ]
                    ; f⁻¹ = \x -> [ x ]
                    ; p = \{xs} -> record { xs' = _
                                          ; p = refl
                                          ; bs =  refl  
                                          ; cs =  zero+ℂ 
                                          }
                    ; p⁻¹ = \{xs} -> record { xs' = _
                                            ; p = refl
                                            ; bs = refl 
                                            ; cs = zero+ℂ
                                            }
                    }

mappend : ∀{n} -> USem n -> USem n -> USem n
mappend {n} u u' = record { f = \xs -> join (map (USem.f u') (USem.f u xs))
                          ; f⁻¹ = \xs -> join (map (USem.f⁻¹ u) (USem.f⁻¹ u' xs))
                          ; p = \{xs} -> record { xs' = _ 
                                                ; p =  refl 
                                                ; bs = silly
                                                ; cs = silly
                                                }
                          ; p⁻¹ = \{xs} -> record { xs' = _ 
                                                  ; p =  refl 
                                                  ; bs = silly
                                                  ; cs = silly
                                                  }
                          }

monoidUSem : ∀{n} -> RawMonoid
monoidUSem {n} = record { carrier = USem n
                        ; _≈_ = _≡_
                        ; _∙_ = mappend
                        ; ε = mempty
                        }

open module mU {n} = RawMonoid (monoidUSem {n}) public


reverse : ∀{n} -> USem n -> USem n
reverse u = record { f = USem.f⁻¹ u
                   ; f⁻¹ = USem.f u
                   ; p = USem.p⁻¹ u
                   ; p⁻¹ = USem.p u
                   }


---------------------------------------------------------------------------------
-- Sep data-type - defines seperability requirement
---------------------------------------------------------------------------------
record ≡Ss {n : ℕ} (xs : List (Base n)) (x : Base n) (q : Qbit n) : Set where
  field
    xs' : List (Base n)
    p : xs ≡ xs'
    bs : map (lookupQ q) xs' ≡ map (lookupQ q) (repeat x (length xs')) 
    cs : foldr _+ℂ_  zeroℂ (map extractℂ xs') ≡ extractℂ x


record Sep {n : ℕ} (i : Qbit n) (u : USem n) : Set where
  field
    s : ∀{x} -> ≡Ss (USem.f u x) x i
    s⁻¹ : ∀{x} -> ≡Ss (USem.f⁻¹ u x) x i

----------------------------------------------------------------------------------

y : Base 2
y = (true ∷ false ∷ []) ∘ oneℂ

y' : Base 2
y' = (true ∷ true ∷ []) ∘ (zeroℂ -ℂ oneℂ)

ys : List (Base 2)
ys = y ∷ y' ∷ y ∷ []

test : ≡Ss ys y qzero
test = record { xs' = _
              ; p = refl
              ; bs = refl
              ; cs = (trans (refl ≡[ _+ℝ_ ]≡ trans (trans (trans com+ℝ zero+ℝ ≡[ _+ℝ_ ]≡ zero+ℝ) com+ℝ) inv+-ℝ) zero+ℝ) ≡:+≡ trans com+ℝ (trans (trans (inv+-ℝ ≡[ _+ℝ_ ]≡ zero+ℝ) zero+ℝ ≡[ _+ℝ_ ]≡ refl) zero+ℝ)
              }