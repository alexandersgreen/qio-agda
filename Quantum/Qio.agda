module Qio  where

open import ListOps
open import USem
open import UReturn
open import URot
open import Swap
open import Cond
open import Ulet
open import Complex

open import Data.Vec hiding (_∷ʳ_; _∷ʳ'_; [_]; sum;_++_) renaming (map to map'')
open import Data.List hiding (sum) renaming (map to map'; _++_ to _+++_)
open import Data.Bool
open import Data.Nat
open import Data.Product hiding (map)
open import Relation.Binary.Core
open import Data.Unit
open import Data.Empty

lift : ∀{n : ℕ} -> Qbit n -> Qbit (suc n)
lift qzero = qzero
lift (qsuc q) = qsuc (lift q)

urot : ∀{n : ℕ} -> (Qbit n) -> Rotation -> USem n
urot qn r = URot qn r UReturn

uId : ∀{n} -> Qbit n -> USem n
uId q = urot q id

uX : ∀{n} -> Qbit n -> USem n
uX q = urot q x

uHad : ∀{n} -> Qbit n -> USem n
uHad q = urot q had

uPhase : ∀{n} -> ℝ -> Qbit n -> USem n
uPhase r q = urot q (phase r)

uswap : ∀{n : ℕ} -> (Qbit n) -> (Qbit n) -> USem n
uswap q1 q2 = Swap q1 q2 UReturn

ucond : ∀{n : ℕ} -> (i : Qbit n) -> (Bool -> (Σ (USem n) (\u -> Sep i u))) -> USem n
ucond q fb = Cond q fb UReturn

ulet : ∀{n : ℕ} -> (b : Bool) -> ((i : (Qbit (suc n))) -> Σ (USem (suc n)) (\u -> Sep i u)) -> USem n
ulet b fq = Ulet b fq UReturn


data QIO (A : Set) : ℕ -> (m : ℕ) -> Set -> Set where
  QReturn : ∀{n : ℕ} -> A -> QIO A n n (Qbit n)
  MkQbit : ∀{n m : ℕ} -> Bool -> ((Qbit (suc n)) -> (QIO A (suc n) m (Qbit m))) -> QIO A n m (Qbit m)
  ApplyU : ∀{n m : ℕ} -> USem n  -> QIO A n m (Qbit m) -> QIO A n m (Qbit m)
  MeasQbit : ∀{n m : ℕ} -> (Qbit n) -> (Bool -> QIO A n m (Qbit m)) -> QIO A n m (Qbit m) 


⊚ : ∀{n : ℕ} -> {A : Set} -> A -> QIO A n n (Qbit n)
⊚ = QReturn

_→⇒→_ : ∀{n m l : ℕ} -> ∀{A B : Set} -> QIO A n m (Qbit m) -> (A -> QIO B m l (Qbit l)) -> QIO B n l (Qbit l)
QReturn a →⇒→ f = f a
MkQbit b g →⇒→ f = MkQbit b (\x -> g x →⇒→ f)
ApplyU u q →⇒→ f = ApplyU u (q →⇒→ f)
MeasQbit x g →⇒→ f = MeasQbit x (\b -> g b →⇒→ f)

runQIO : ∀{n m : ℕ} -> ∀{A : Set} -> QIO A n m (Qbit m) -> List (Base n) -> List (A × List (Base m))
runQIO (QReturn a) v = [ a , v ]
runQIO {n} {m} (MkQbit b fq) v = runQIO (fq (newQbit n)) (map' (\x -> x ∷ʳ' b) v)
runQIO (ApplyU u q) v = runQIO q (map (USem.f u) v)
runQIO (MeasQbit q fb) v = (runQIO (fb false) (filter (\b -> not (lookupQ q b)) v)) +++ (runQIO (fb true) (filter (\b -> (lookupQ q b)) v))

run' : ∀{n : ℕ} -> ∀{A : Set} -> QIO A zero n (Qbit n) -> List (A × List (Base n))
run' q = runQIO q [ emptyBase ]

--[|_|²]
sum : ∀{n} -> List (Base n) -> ℝ
sum [] = zeroℝ
sum (y ∘ y' ∷ xs) = [| y' |²] +ℝ sum xs

combine : ∀{n : ℕ} -> ∀{A : Set} -> List (A × List (Base n)) -> List (A × ℝ)
combine [] = []
combine ((a , []) ∷ xs) = combine xs
combine ((a , x ∷ xs) ∷ xs') = Data.List._∷_ ((a ,  sum (x ∷ xs))) ((combine xs'))

run : ∀{n : ℕ} -> ∀{A : Set} -> QIO A zero n (Qbit n) -> List (A × ℝ)
run q = combine (run' q)

return : ∀{A : Set} -> A -> List (A × ℝ)
return a = [ a , oneℝ ]

mkQbit : ∀{n : ℕ} -> Bool -> QIO (Qbit (suc n)) n (suc n) (Qbit (suc n))
mkQbit b = MkQbit b (\q -> QReturn q)  

applyU : ∀{n : ℕ} -> USem n -> QIO ⊤ n n (Qbit n)
applyU u = ApplyU u (QReturn tt)

measQbit : ∀{n : ℕ} -> Qbit n -> QIO Bool n n (Qbit n)
measQbit x = MeasQbit x (\b -> QReturn b)

true' : QIO Bool zero _ _
true' = mkQbit true →⇒→ \q ->
        measQbit q

false' : QIO Bool zero _ _
false' = mkQbit false →⇒→ \q ->
         measQbit q

false'' : QIO Bool zero _ _
false'' = mkQbit false →⇒→ \q -> 
          applyU (uX q  ∙ uX q) →⇒→ \_ ->
          measQbit q

|+> : ∀{n} -> QIO (Qbit (suc n)) n _ _
|+> = mkQbit false →⇒→ \q ->
      applyU (uHad q) →⇒→ \_ ->
      ⊚ q

|-> : ∀{n} -> QIO (Qbit (suc n)) n _ _
|-> = mkQbit true →⇒→ \q ->
      applyU (uHad q) →⇒→ \_ ->
      ⊚ q

rand : QIO Bool zero _ _
rand = |+> →⇒→ \q ->
       measQbit q

hadTwice : QIO Bool zero _ _
hadTwice = |+> →⇒→ \q ->
           applyU (uHad q) →⇒→ \_ ->
           measQbit q

postulate
  shareP : ∀{n b} -> (q q' : Qbit (suc (suc n))) -> Sep  q (if b then uX q' else UReturn)

share : ∀{n} -> Qbit (suc n) -> QIO (Qbit (suc (suc n))) (suc n) _ _
share {n} q = mkQbit false →⇒→ \q' ->
              applyU (ucond (lift q) (\b -> (if b then (uX q') else UReturn) , shareP {n} {b} (lift q) q')) →⇒→ \_ ->
              ⊚ q' 

bell : ∀{n} -> QIO (Qbit (suc (suc n)) × Qbit (suc (suc n))) n _ _
bell = |+> →⇒→ \q ->
       share q →⇒→ \q' -> 
       ⊚ (lift q , q')

measPair : ∀{n} -> (Qbit (suc n) × Qbit (suc n)) -> QIO (Bool × Bool) (suc n) _ _
measPair (x , y) = measQbit x →⇒→ \b ->
                   measQbit y →⇒→ \b' ->
                   ⊚ (b , b') 

measBell : QIO (Bool × Bool) zero _ _
measBell = bell →⇒→ \qq' ->
           measPair qq'

postulate
  deutschP : ∀{n b} -> (f : Bool -> Bool) -> (q q' : Qbit (suc (suc n))) -> Sep q (if f b then uX q' else UReturn)

deutsch : (Bool -> Bool) -> QIO Bool zero _ _
deutsch f = |+> →⇒→ \q1 ->
            |-> →⇒→ \q2 ->
            applyU (ucond (lift q1) (\b -> (if (f b) then (uX q2) else UReturn) 
                   , deutschP {zero} {b} f (lift q1) q2)) →⇒→ \_ ->
            applyU (uHad (lift q1)) →⇒→ \_ ->
            measQbit (lift q1) 

--------- teleportation

alice : ∀{n} -> Qbit (suc (suc n)) -> Qbit (suc (suc n)) -> QIO (Bool × Bool) (suc (suc n)) _ _
alice {n} aq eq = applyU (ucond aq (\a -> ((if a then uX eq else UReturn) , shareP {n} {a} aq eq))) →⇒→ \_ ->
                  applyU (uHad aq) →⇒→ \_ ->
                  measPair (aq , eq)

bobsU : ∀{n} -> Bool × Bool -> (Qbit n) -> USem n
bobsU (true , true) q = uX q ∙ uPhase pi q
bobsU (true , false) q = uPhase pi q
bobsU (false , true) q = uX q
bobsU (false , false) q = UReturn 

bob : ∀{n} -> Qbit n -> (Bool × Bool) -> QIO (Qbit n) n _ _
bob q cd = applyU (bobsU cd q) →⇒→ \_ -> 
           ⊚ q  

teleportation : ∀{n} -> Qbit n -> QIO (Qbit (suc (suc n))) n _ _
teleportation iq  =  bell →⇒→ \eqs ->
                     alice (lift (lift iq)) (proj₁ eqs) →⇒→ \cd ->
                     bob (proj₂ eqs) cd


teleportBool : ∀{n} -> Bool -> QIO Bool n _ _
teleportBool b = mkQbit b →⇒→ \iq ->
                 teleportation iq →⇒→ \tq ->
                 measQbit tq



 
