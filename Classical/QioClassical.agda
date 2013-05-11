module QioClassical where

open import USem
open import UReturn
open import X
open import Swap
open import Cond
open import Ulet

open import Data.Vec hiding (_∷ʳ_; _>>=_)
open import Data.List hiding (and; [_]; map)
open import Data.Bool
open import Data.Nat hiding (_≤_)
open import Data.Product hiding (map; ,_)
open import Relation.Binary.Core
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Category.Monad.Indexed


lift≢ : ∀{n} -> {x y : Qbit n} -> (qsuc x ≢ qsuc y) -> (x ≢ y)
lift≢ {zero} {()} {()} p 
lift≢ {suc n} {qzero} {qzero} p with p refl
...| ()
lift≢ {suc n} {qzero} {qsuc i} p = \x -> p (cong qsuc x)
lift≢ {suc n} {qsuc i} {qzero} p = \x -> p (cong qsuc x)
lift≢ {suc n} {qsuc i} {qsuc i'} p = \x -> p (cong qsuc x)

ux : ∀{n : ℕ} -> (Qbit n) -> USem n
ux qn = X qn ε 

uswap : ∀{n : ℕ} -> (Qbit n) -> (Qbit n) -> USem n
uswap q1 q2 = Swap q1 q2 ε

ucond : ∀{n : ℕ} -> (i : Qbit n) -> (Bool -> (Σ (USem n) (\u -> Sep i u))) -> USem n
ucond q fb = Cond q fb ε

ulet : ∀{n : ℕ} -> (b : Bool) -> ((i : (Qbit (suc n))) -> (Σ (USem (suc n)) (\u -> Sep {suc n} i u))) -> USem n
ulet b fq = Ulet b fq ε

data Either (A B : Set) : Set where
  inL : A -> Either A _
  inR : B -> Either _ B

cong' : ∀{m n} -> (suc m ≡ suc n) -> m ≡ n
cong' {n} {.n} refl = refl

_≡≢_ : (m n : ℕ) -> Either (m ≡ n) (m ≢ n)
zero ≡≢ zero = inL refl
zero ≡≢ suc n = inR \()
suc m ≡≢ zero = inR \()
suc m ≡≢ suc n with m ≡≢ n
suc .n ≡≢ suc n | inL refl = inL refl
suc m ≡≢ suc n | inR p = inR (\x -> p (cong' x))

data IsLessEqual : ℕ -> ℕ -> Set where
 Equal : ∀{n} -> IsLessEqual n n
 Less : ∀{m n} -> IsLessEqual m n -> IsLessEqual m (suc n) 

lift1 : ∀{n : ℕ} -> Qbit n -> Qbit (suc n)
lift1 qzero = qzero
lift1 (qsuc q) = qsuc (lift1 q)

lift : ∀{m n} -> IsLessEqual m n -> Qbit m -> Qbit n
lift Equal q = q
lift (Less i) q = lift1 (lift i q)

_≤_ : ℕ -> ℕ -> Bool
zero ≤ n = true
suc m ≤ zero = false
suc m ≤ suc n with suc m ≡≢ suc n
suc .n ≤ suc n | inL refl = true
suc m ≤ suc n | inR q = suc m ≤ n

equiv→ : (m n : ℕ) -> T (m ≤ n) -> IsLessEqual m n
equiv→ zero zero p = Equal
equiv→ (suc m) zero ()
equiv→ zero (suc n) p = Less (equiv→ zero n p)
equiv→ (suc m) (suc n) p with (suc m) ≡≢ (suc n)
equiv→ (suc .n) (suc n) p | inL refl = Equal
equiv→ (suc m) (suc n) p | inR p' = Less (equiv→ (suc m) n p)


data QIO (A : Set) : ℕ -> ℕ -> Set where
  QReturn : ∀{n : ℕ} -> A -> QIO A n n
  MkQbit : ∀{n m : ℕ} -> Bool -> (Qbit (suc n) -> (QIO A (suc n) m)) -> QIO A n m
  ApplyU : ∀{l m n : ℕ} ->  Vec (Qbit m) l -> (Vec (Qbit m) l -> USem m)  -> QIO A m n -> QIO A m n
  MeasQbit : ∀{n m : ℕ} -> (Qbit n) -> (Bool -> QIO A n m) -> QIO A n m 


QIObind : ∀{n m l : ℕ} -> ∀{A B : Set} -> QIO A n m -> (A -> QIO B m l) -> QIO B n l
QIObind (QReturn a) f = f a
QIObind (MkQbit b g) f = MkQbit b (\x -> QIObind (g x) f)
QIObind (ApplyU qs u q) f = ApplyU qs u (QIObind q f)
QIObind (MeasQbit x g) f = MeasQbit x (\b -> QIObind (g b) f)

monadQIO : RawIMonad {ℕ} (\m n A -> QIO A m n)
monadQIO = record { return = QReturn
                  ; _>>=_ = QIObind
                  }

open module mQIO = RawIMonad monadQIO

Qbits : ℕ -> Set
Qbits n = Vec (Σ ℕ Qbit) n

greatest' : ℕ -> ℕ -> ℕ
greatest' zero n = n
greatest' (suc n) zero = suc n
greatest' (suc n) (suc n') = suc (greatest' n n')

greatest : ∀{n} -> Qbits n -> ℕ
greatest [] = zero
greatest ((n , qn) ∷ qs) with greatest qs
...| m = greatest' n m

eq : ∀{n} -> T (n ≤ n)
eq {zero} = _
eq {suc n} with suc n ≡≢ suc n
eq {suc n} | inL refl = _
eq {suc n} | inR y with y refl
...| ()

normalise' : ∀{n m} -> {qs : Qbits n} -> {p : T (greatest qs ≤ m)} -> Vec (Qbit m) n
normalise' {zero} {m} {[]} = []
normalise' {(suc n)} {m} {x ∷ xs} {p} = {!!}

normalise : ∀{n} -> (qs : Qbits n) -> Vec (Qbit (greatest qs)) n
normalise {n} qs = normalise' {n} {greatest qs} {qs} {eq {greatest qs}}

mkQbit : ∀{n : ℕ} -> Bool -> QIO (Qbit (suc n)) n (suc n)
mkQbit b = MkQbit b QReturn  

applyU' : ∀{l m n : ℕ} -> {p : T (m ≤ n)} -> Vec (Qbit m) l -> (Vec (Qbit n) l -> USem n) -> QIO ⊤ n n
applyU' {l} {m} {n} {p} qs u = ApplyU (map (lift (equiv→ m n p)) qs) u (QReturn tt)

applyU : ∀{l m n : ℕ} -> {p : T (m ≤ n)} -> Vec (Qbit m) l -> (Vec (Qbit n) l -> USem n) -> QIO ⊤ n n
applyU {l} {m} {n} {p} qs u = ApplyU (map (lift (equiv→ m n p)) qs) u (QReturn tt)

measQbit : ∀{m n : ℕ} -> {p : T (m ≤ n)} -> Qbit m -> QIO Bool n n
measQbit {m} {n} {p} q = MeasQbit (lift (equiv→ m n p) q) QReturn

runQIO : ∀{n m : ℕ} -> ∀{A : Set} -> QIO A n m -> Vec Bool n -> A
runQIO (QReturn a) v = a
runQIO {n} {m} (MkQbit b fq) v = runQIO (fq (newQbit n)) (v ∷ʳ b)
runQIO (ApplyU qs u q) v = runQIO q ((USem.f (u qs)) v)
runQIO (MeasQbit q fb) v = runQIO (fb (v !! q)) v 

runQIO' : ∀{n m : ℕ} -> ∀{A : Set} -> QIO A n m -> Vec Bool n -> Vec Bool m
runQIO' (QReturn a) v = v
runQIO' {n} {m} (MkQbit b fq) v = runQIO' (fq (newQbit n)) (v ∷ʳ b)
runQIO' (ApplyU qs u q) v = runQIO' q ((USem.f (u qs)) v)
runQIO' (MeasQbit q fb) v = runQIO' (fb (v !! q)) v 

runC : ∀{m : ℕ} -> ∀{A : Set} -> QIO A zero m -> A
runC q = runQIO q []

runC' : ∀{m : ℕ} -> ∀{A : Set} -> QIO A zero m -> Vec Bool m
runC' q = runQIO' q []


false' : QIO Bool zero _ 
false' = mkQbit false >>= \q -> 
         applyU [ q ] (\qs -> ux q  ∙ ux q) >>
         measQbit q

falseP : runC false' ≡ false
falseP = refl

qif : ∀{n : ℕ} -> (i : Qbit n) -> (u : USem n) -> Sep {n} i u -> USem n
qif {n} i u s = ucond i (\b -> if b then u , s else  ε , 
                        record  { s = refl
                                ; s⁻¹ = refl 
                                })

cnotP : ∀{n} -> (xs : Vec Bool n) -> (cq q : Qbit n) -> (cq ≢ q) -> negate q xs !! cq ≡ xs !! cq
cnotP [] () () p
cnotP (x ∷ xs) qzero qzero p with p refl
...| ()
cnotP (x ∷ xs) qzero (qsuc i) p = refl
cnotP (x ∷ xs) (qsuc i) qzero p = refl
cnotP (x ∷ xs) (qsuc i) (qsuc i') p = cnotP xs i i' (lift≢ p)

cnot : ∀{n : ℕ} -> (cq q : Qbit n) -> (cq ≢ q) -> USem n
cnot {n} cq q p = qif cq (ux q) (record  { s = \{xs} -> cnotP xs cq q p
                                         ; s⁻¹ = \{xs} -> cnotP xs cq q p
                                         })

toffoliP : ∀{n : ℕ} -> (xs : Vec Bool n) -> (q1 q2 q3 : Qbit n) -> (q1 ≢ q3) -> (cnp : q2 ≢ q3) -> USem.f (cnot q2 q3 cnp) xs !! q1 ≡ xs !! q1
toffoliP xs q1 q2 q3 p cnp with xs !! q2
...| true = cnotP xs q1 q3 p
...| false = refl

toffoliPR : ∀{n : ℕ} -> (xs : Vec Bool n) -> (q1 q2 q3 : Qbit n) -> (q1 ≢ q3) -> (cnp : q2 ≢ q3) -> USem.f⁻¹ (cnot q2 q3 cnp) xs !! q1 ≡ xs !! q1
toffoliPR xs q1 q2 q3 p cnp with xs !! q2
...| true = cnotP xs q1 q3 p
...| false = refl

toffoli' : ∀{n : ℕ} -> (q1 q2 q3 : Qbit n) -> (q1 ≢ q3) -> (q2 ≢ q3) -> USem n 
toffoli' {n} q1 q2 q3 p cnp = qif q1 (cnot q2 q3 cnp) (record  { s = \{xs} -> toffoliP xs q1 q2 q3 p cnp
                                                                  ; s⁻¹ =  \{xs} -> toffoliPR xs q1 q2 q3 p cnp
                                                                  })
postulate
  [-_≢_-] : ∀{n} -> (qx qy : Qbit n) -> qx ≢ qy

toffoli : ∀{n} -> (Vec (Qbit n) 3) -> USem n
toffoli (q1 ∷ q2 ∷ q3 ∷ []) = toffoli' q1 q2 q3 [- q1 ≢ q3 -] [- q2 ≢ q3 -]

_and_ : Bool -> Bool -> QIO Bool _ _
x and y = mkQbit x >>= \qx ->
          mkQbit y >>= \qy ->
          mkQbit false >>= \qf ->
          applyU [ qx ] (\x -> (toffoli' (lift1 (lift1 qx)) (lift1 qy) qf 
              [- lift1 (lift1 qx) ≢ qf -] 
              [- lift1 qy ≢ qf -]))       >>
          measQbit qf 

_and'_ : Bool -> Bool -> QIO Bool zero _
x and' y = mkQbit false >>= \qf ->
           mkQbit x     >>= \qx ->
           mkQbit y     >>= \qy ->
           applyU ((lift1 qx) ∷ qy ∷ (lift1 (lift1 qf)) ∷ []) toffoli >>
           measQbit qf

andproof : ∀{a b : Bool} -> a ∧ b ≡ runC (a and b)
andproof {true} {true} = refl
andproof {true} {false} = refl
andproof {false} {true} = refl
andproof {false} {false} = refl

