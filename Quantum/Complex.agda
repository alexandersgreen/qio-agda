module Complex where
-- Complex numbers

open import Relation.Binary.Core 
open import Data.Product hiding (_×_)
open import Relation.Binary.PropositionalEquality


--transitivity is used to construct proofs
_■_ : ∀{A : Set} -> ∀{a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
refl ■ refl = refl

infixr 5 _■_

data ℝ : Set where
{-# COMPILED_DATA ℝ Float #-}

--postulate all the field axioms for ℝ

postulate
  zeroℝ : ℝ  -- additive identity
  oneℝ : ℝ   -- multiplicative identity
  _+ℝ_ : ℝ -> ℝ -> ℝ -- gives closure under addition
  -ℝ : ℝ -> ℝ -- gives additive inverse 
  _×ℝ_ : ℝ -> ℝ -> ℝ -- gives closure under multiplication
  ÷ℝ : ℝ -> ℝ -- gives multiplicative inverse
{-# COMPILED zeroℝ 0.0 :: Float #-}
{-# COMPILED oneℝ 1.0 :: Float #-}
{-# COMPILED _+ℝ_ (+) :: Float -> Float -> Float #-}
{-# COMPILED -ℝ (0.0 -) :: Float -> Float #-}
{-# COMPILED _×ℝ_ (*) :: Float -> Float -> Float #-}
{-# COMPILED ÷ℝ (1.0 /) :: Float -> Float #-}
  
postulate
  -- addition is associative
  assoc+ℝ : ∀{a b c : ℝ} -> a +ℝ (b +ℝ c) ≡ (a +ℝ b) +ℝ c
  -- multiplication is associative
  assoc×ℝ : ∀{a b c : ℝ} -> a ×ℝ (b ×ℝ c) ≡ (a ×ℝ b) ×ℝ c
  -- addition is commutative
  com+ℝ : ∀{a b : ℝ} -> a +ℝ b ≡ b +ℝ a
  -- multiplication is commutative
  com×ℝ : ∀{a b : ℝ} -> a ×ℝ b ≡ b ×ℝ a
  -- zeroℝ is additive identity
  zero+ℝ : ∀{a : ℝ} -> a +ℝ zeroℝ ≡ a
  -- oneℝ is multiplicative identity
  one×ℝ : ∀{a : ℝ} -> a ×ℝ oneℝ ≡ a
  -- subtraction is additive inverse
  inv+-ℝ : ∀{a : ℝ} -> a +ℝ (-ℝ a) ≡ zeroℝ
  -- division (except by zeroℝ ????) is multiplicative inverse
  inv×÷ℝ : ∀{a : ℝ} -> a ×ℝ (÷ℝ a) ≡ oneℝ
  -- distributivity of multiplication over addition
  dist×+ℝ : ∀{a b c : ℝ} -> a ×ℝ (b +ℝ c) ≡ (a ×ℝ b) +ℝ (a ×ℝ c)

-- equality distributes over binary operations on ℝ
_≡[_]≡_ : {A : Set} -> ∀{a b c d : A} -> (a ≡ c) -> (_op_ : A -> A -> A) -> (b ≡ d) -> (a op b) ≡ (c op d)
refl ≡[ _ ]≡ refl = refl

-- equality distributes through additive inverse
-ℝ≡ : ∀{a b : ℝ} -> (a ≡ b) -> (-ℝ a) ≡ (-ℝ b)
-ℝ≡ refl = refl

-- addition respects equivalence
_+ℝ≡_ : ∀{a b : ℝ} -> (c : ℝ) -> (a +ℝ c) ≡ (b +ℝ c) -> a ≡ b
c +ℝ≡ refl = refl

-- -ℝ distributes over +ℝ
dist-+ℝ : ∀{a b : ℝ} -> -ℝ (a +ℝ b) ≡ (-ℝ a) +ℝ (-ℝ b)
dist-+ℝ {a} {b} = (a +ℝ b) +ℝ≡ ( -- now need -ℝ (a +ℝ b) +ℝ (a +ℝ b) ≡ ... ≡ ((-ℝ a) +ℝ (-ℝ b)) +ℝ (a +ℝ b)
                                 com+ℝ                 --> ≡ (a +ℝ b) +ℝ -ℝ (a + ℝ b) 
                               ■ inv+-ℝ                --> ≡ zeroℝ
                               ■ sym  
                                     ( com+ℝ 
                                     ■ inv+-ℝ 
                                     )                 --> ≡ (-ℝ a) +ℝ a
                               ■ refl ≡[ _+ℝ_ ]≡ sym 
                                                     ( com+ℝ 
                                                     ■ zero+ℝ 
                                                     ) --> ≡ (-ℝ a) +ℝ (zeroℝ +ℝ a) 
                               ■ refl ≡[ _+ℝ_ ]≡ (
                                                  ( sym 
                                                        inv+-ℝ
                                                      ■ com+ℝ
                                                  ) ≡[ _+ℝ_ ]≡ refl
                                                 ) --> ≡ (-ℝ a) +ℝ (((-ℝ b) +ℝ b) +ℝ a)
                               ■ refl ≡[ _+ℝ_ ]≡ 
                                                 ( sym 
                                                       assoc+ℝ
                                                 ) --> ≡ (-ℝ a) +ℝ ((-ℝ b) +ℝ (b +ℝ a))
                               ■ refl ≡[ _+ℝ_ ]≡ 
                                                 (refl ≡[ _+ℝ_ ]≡ 
                                                                 sym 
                                                                     com+ℝ
                                                 ) --> ≡ (-ℝ a) +ℝ ((-ℝ b) +ℝ (a +ℝ b))
                               ■ assoc+ℝ           --> ≡ ((-ℝ a) +ℝ (-ℝ b)) +ℝ (a +ℝ b)
                               )
                                 


-- a ×ℝ zeroℝ ≡ zeroℝ
zero×ℝ : ∀{a : ℝ} -> a ×ℝ zeroℝ ≡ zeroℝ
zero×ℝ {a} = a +ℝ≡ ( -- now need (a ×ℝ zeroℝ) +ℝ a ≡ zeroℝ +ℝ a
                     refl ≡[ _+ℝ_ ]≡ 
                                    sym 
                                        one×ℝ --> ≡ (a ×ℝ zeroℝ) +ℝ (a ×ℝ oneℝ)
                   ■ sym 
                         dist×+ℝ              --> ≡ a ×ℝ (zeroℝ +ℝ oneℝ)
                   ■ refl ≡[ _×ℝ_ ]≡ 
                                     ( com+ℝ 
                                     ■ zero+ℝ
                                     )        --> ≡ a ×ℝ oneℝ
                   ■ one×ℝ                    --> ≡ a
                   ■ sym 
                         zero+ℝ               --> ≡ a +ℝ zeroℝ
                   ■ com+ℝ                    --> ≡ zeroℝ +ℝ a
                   )

-- -ℝ distributes over ×ℝ
dist-×ℝ : ∀{a b : ℝ} -> -ℝ (a ×ℝ b) ≡ (-ℝ a) ×ℝ b
dist-×ℝ {a} {b} = (a ×ℝ b) +ℝ≡ ( -- now need -ℝ (a ×ℝ b) +ℝ (a ×ℝ b) ≡ ((-ℝ a) ×ℝ b) +ℝ (a ×ℝ b)
                                 com+ℝ                     --> ≡ (a ×ℝ b) +ℝ -ℝ (a ×ℝ b)
                               ■ inv+-ℝ                    --> ≡ zeroℝ
                               ■ sym 
                                     zero×ℝ                --> ≡ b ×ℝ zeroℝ
                               ■ refl ≡[ _×ℝ_ ]≡ 
                                                sym 
                                                    inv+-ℝ --> b ×ℝ (a +ℝ (-ℝ a))
                               ■ refl ≡[ _×ℝ_ ]≡ 
                                                com+ℝ      --> b ×ℝ ((-ℝ a) +ℝ a)          
                               ■ dist×+ℝ                   --> (b ×ℝ (-ℝ a)) +ℝ (b ×ℝ a)
                               ■ com×ℝ 
                                      ≡[ _+ℝ_ ]≡ 
                                                com×ℝ      --> ((-ℝ a) ×ℝ b) +ℝ (a ×ℝ b)
                               )

-- -ℝ zeroℝ ≡ zeroℝ
-zeroℝ : -ℝ zeroℝ ≡ zeroℝ
-zeroℝ =   sym 
               zero+ℝ  --> (-ℝ zeroℝ) + zeroℝ
         ■ com+ℝ       --> zeroℝ +ℝ (-ℝ zeroℝ)
         ■ inv+-ℝ      --> zeroℝ

-- ­ℝ is self inverse
-ℝ-ℝ : ∀{a : ℝ} -> -ℝ (-ℝ a) ≡ a
-ℝ-ℝ {a} = -ℝ a +ℝ≡ ( --now need -ℝ (-ℝ a) +ℝ -ℝ a ≡ a + -ℝ a
                      com+ℝ      --> -ℝ a +ℝ -ℝ (-ℝ a)
                    ■ inv+-ℝ     --> zeroℝ
                    ■ sym 
                          inv+-ℝ --> a + -ℝ a
                    )

data ℂ : Set where
  _:+_ : ℝ -> ℝ -> ℂ

-- equality distributes over :+ 
_≡:+≡_ : ∀{a a' b b' : ℝ} -> (a ≡ b) -> (a' ≡ b') -> (a :+ a') ≡ (b :+ b')
refl ≡:+≡ refl = refl
 
ℝ⟶ℂ : ℝ -> ℂ
ℝ⟶ℂ a = a :+ zeroℝ

zeroℂ : ℂ -- additive identity of ℂ
zeroℂ = ℝ⟶ℂ zeroℝ

oneℂ : ℂ -- multiplicative identity of ℂ
oneℂ = ℝ⟶ℂ oneℝ

_+ℂ_ : ℂ -> ℂ -> ℂ -- closed under addition
(a :+ b) +ℂ (a' :+ b') = (a +ℝ a') :+ (b +ℝ b')

--addition is asociative
assoc+ℂ : ∀{a b c : ℂ} -> a +ℂ (b +ℂ c) ≡ (a +ℂ b) +ℂ c
assoc+ℂ {a :+ ai} {b :+ bi} {c :+ ci} = assoc+ℝ 
                                      ≡:+≡ 
                                        assoc+ℝ

--addition is commutative
com+ℂ : ∀{a b : ℂ} -> a +ℂ b ≡ b +ℂ a
com+ℂ {a :+ ai} {b :+ bi} = com+ℝ 
                          ≡:+≡ 
                            com+ℝ

_-ℂ_ : ℂ -> ℂ -> ℂ 
(a :+ b) -ℂ (a' :+ b') = (a +ℝ (-ℝ a')) :+ (b +ℝ (-ℝ b'))

--subtraction is additive inverse
inv+-ℂ : ∀{a : ℂ} -> a -ℂ a ≡ zeroℂ
inv+-ℂ {a :+ ai} = inv+-ℝ 
                 ≡:+≡ 
                   inv+-ℝ
 
_×ℂ_ : ℂ -> ℂ -> ℂ -- closed under multiplication
(a :+ b) ×ℂ (a' :+ b') = ((a ×ℝ a') +ℝ (-ℝ (b ×ℝ b'))) :+ ((a ×ℝ b') +ℝ (b ×ℝ a'))

--assoc×ℂ' : ∀{a b c : ℂ} -> a ×ℂ (b ×ℂ c) ≡ (a ×ℂ b) ×ℂ c
--assoc×ℂ' {a :+ ai} {b :+ bi} {c :+ ci} = {!!} ≡:+≡ {!!}

--multiplication is associative
assoc×ℂ : ∀{a b c : ℂ} -> a ×ℂ (b ×ℂ c) ≡ (a ×ℂ b) ×ℂ c
assoc×ℂ {a :+ ai} {b :+ bi} {c :+ ci} = (-- real part is (a ×ℝ ((b ×ℝ c) +ℝ -ℝ (bi ×ℝ ci))) +ℝ -ℝ (ai ×ℝ ((b ×ℝ ci) +ℝ (bi ×ℝ c))) 
                                         --            ≡ (((a ×ℝ b) +ℝ -ℝ (ai ×ℝ bi)) ×ℝ c) +ℝ -ℝ (((a ×ℝ bi) +ℝ (ai ×ℝ b)) ×ℝ ci)
                                          dist×+ℝ 
                                         ≡[ _+ℝ_ ]≡ 
                                          -ℝ≡ 
                                             dist×+ℝ
                                        ■ sym 
                                              assoc+ℝ 
                                        ■  ( 
                                             assoc×ℝ 
                                           ■ com×ℝ
                                           ) 
                                          ≡[ _+ℝ_ ]≡ 
                                           (
                                             refl ≡[ _+ℝ_ ]≡ dist-+ℝ 
                                           ■ assoc+ℝ 
                                           ■ ( 
                                              ( 
                                                refl ≡[ _×ℝ_ ]≡ ( 
                                                                 -ℝ≡ 
                                                                     com×ℝ 
                                                                   ■ dist-×ℝ
                                                                ) 
                                              ■ (
                                                  assoc×ℝ 
                                                ■ com×ℝ ≡[ _×ℝ_ ]≡ refl
                                                ■ sym assoc×ℝ
                                                ■ sym dist-×ℝ
                                                )
                                              ) 
                                             ≡[ _+ℝ_ ]≡ 
                                              -ℝ≡ 
                                                 ( assoc×ℝ 
                                                 ■ com×ℝ
                                                 )                             
                                             ) 
                                            ≡[ _+ℝ_ ]≡ 
                                             (
                                               dist-×ℝ 
                                             ■ assoc×ℝ 
                                             ■ com×ℝ 
                                             ■ refl ≡[ _×ℝ_ ]≡ sym dist-×ℝ
                                             ) 
                                           ■ com+ℝ 
                                           ■ sym refl ≡[ _+ℝ_ ]≡ sym dist-+ℝ
                                           ) 
                                        ■ assoc+ℝ 
                                        ■ sym ( com×ℝ 
                                               ■ dist×+ℝ
                                               ) 
                                          ≡[ _+ℝ_ ]≡ 
                                          sym ( -ℝ≡ com×ℝ 
                                               ■ -ℝ≡ dist×+ℝ
                                               ) 
                                        )
                                        ≡:+≡ --imaginary part is ((a ×ℝ ((b ×ℝ ci) +ℝ (bi ×ℝ c))) +ℝ (ai ×ℝ ((b ×ℝ c) +ℝ -ℝ (bi ×ℝ ci))) ≡ (((a ×ℝ b) +ℝ -ℝ (ai ×ℝ bi)) ×ℝ ci) +ℝ (((a ×ℝ bi) +ℝ (ai ×ℝ b)) ×ℝ c))
                                        trans (dist×+ℝ ≡[ _+ℝ_ ]≡ dist×+ℝ) (trans (trans (sym assoc+ℝ) (trans (trans assoc×ℝ com×ℝ ≡[ _+ℝ_ ]≡ trans (trans (trans assoc×ℝ com×ℝ ≡[ _+ℝ_ ]≡ (trans assoc×ℝ com×ℝ ≡[ _+ℝ_ ]≡ trans (refl ≡[ _×ℝ_ ]≡ dist-×ℝ) (trans (trans com×ℝ (trans (trans (sym assoc×ℝ) (trans (refl ≡[ _×ℝ_ ]≡ com×ℝ) assoc×ℝ)) com×ℝ)) (refl ≡[ _×ℝ_ ]≡ trans (sym dist-×ℝ) (-ℝ≡ com×ℝ))))) assoc+ℝ) com+ℝ) assoc+ℝ)) (sym (trans com×ℝ dist×+ℝ ≡[ _+ℝ_ ]≡ trans com×ℝ dist×+ℝ)))

--multiplication is commutative
com×ℂ : ∀{a b : ℂ} -> a ×ℂ b ≡ b ×ℂ a
com×ℂ {a :+ ai} {b :+ bi} = (com×ℝ ≡[ _+ℝ_ ]≡ -ℝ≡ com×ℝ) 
                            ≡:+≡ 
                            (trans com+ℝ ((com×ℝ ≡[ _+ℝ_ ]≡ com×ℝ)))

-- zeroℂ is additive identity
zero+ℂ : ∀{a : ℂ} -> a +ℂ zeroℂ ≡ a
zero+ℂ {a :+ ai} = zero+ℝ ≡:+≡ zero+ℝ

-- oneℂ is multiplicative identity
one×ℂ : ∀{a : ℂ} -> a ×ℂ oneℂ ≡ a
one×ℂ {a :+ ai} = trans (one×ℝ ≡[ _+ℝ_ ]≡ trans (-ℝ≡ zero×ℝ) -zeroℝ) zero+ℝ 
                  ≡:+≡ 
                  trans (zero×ℝ ≡[ _+ℝ_ ]≡ one×ℝ) (trans com+ℝ zero+ℝ)

conjugate : ℂ -> ℂ
conjugate (a :+ b) = a :+ (-ℝ b)

2conjugate : {c : ℂ} -> conjugate (conjugate c) ≡ c
2conjugate {(y :+ y')} = refl ≡:+≡ -ℝ-ℝ

_ℂ÷ℝ_ : ℂ -> ℝ -> ℂ
(a :+ b) ℂ÷ℝ x = (a ×ℝ (÷ℝ x)) :+ (b ×ℝ (÷ℝ x))

--(a+ib)/(a'+ib')=(aa'+bb' :+ (ba'-ab'))/(a'^2+b'^2)
_÷ℂ_ : ℂ -> ℂ -> ℂ
(a :+ b) ÷ℂ (a' :+ b') =(((a ×ℝ a') +ℝ (b ×ℝ b')) :+ ((b ×ℝ a') +ℝ (-ℝ (a ×ℝ b')))) 
                        ℂ÷ℝ 
                        ((a' ×ℝ a') +ℝ (b' ×ℝ b'))

-- division (except by zeroℝ ????) is multiplicative inverse
inv×÷ℂ : ∀{a : ℂ} -> a ÷ℂ a ≡ oneℂ
inv×÷ℂ {a :+ ai} = inv×÷ℝ 
                   ≡:+≡ 
                   trans (trans (com×ℝ ≡[ _+ℝ_ ]≡ refl) inv+-ℝ ≡[ _×ℝ_ ]≡ refl) (trans com×ℝ zero×ℝ)

-- distributivity of multiplication over addition
dist×+ℂ : ∀{a b c : ℂ} -> a ×ℂ (b +ℂ c) ≡ (a ×ℂ b) +ℂ (a ×ℂ c)
dist×+ℂ {a :+ ai} {b :+ bi} {c :+ ci} = trans (dist×+ℝ ≡[ _+ℝ_ ]≡ -ℝ≡ dist×+ℝ) (trans com+ℝ (trans assoc+ℝ (trans ((dist-+ℝ ≡[ _+ℝ_ ]≡ refl) ≡[ _+ℝ_ ]≡ refl) (trans (trans (trans (trans (sym assoc+ℝ) (refl ≡[ _+ℝ_ ]≡ com+ℝ)) assoc+ℝ ≡[ _+ℝ_ ]≡ refl) (sym assoc+ℝ)) (com+ℝ ≡[ _+ℝ_ ]≡ com+ℝ))))) 
                                        ≡:+≡ 
                                        trans (dist×+ℝ ≡[ _+ℝ_ ]≡ dist×+ℝ) (trans assoc+ℝ (trans (trans (sym assoc+ℝ) (trans (refl ≡[ _+ℝ_ ]≡ com+ℝ) assoc+ℝ) ≡[ _+ℝ_ ]≡ refl) (sym assoc+ℝ)))


a:+zeroℝ+ℂb:+zeroℝ : ∀{a b : ℝ} -> (a :+ zeroℝ) +ℂ (b :+ zeroℝ) ≡ (a +ℝ b) :+ zeroℝ
a:+zeroℝ+ℂb:+zeroℝ {a} {b} = refl ≡:+≡ zero+ℝ 

postulate 
  pi : ℝ
  sqrt2 : ℝ
  sinℝ : ℝ -> ℝ
  expℝ : ℝ -> ℝ
{-# COMPILED pi pi :: Float #-}
{-# COMPILED sqrt2 (sqrt 2) :: Float #-}
{-# COMPILED sinℝ sin :: Float -> Float #-}
{-# COMPILED expℝ exp :: Float -> Float #-}

pi/2 : ℝ
pi/2 = (pi ×ℝ (÷ℝ (oneℝ +ℝ oneℝ)))

cosℝ : ℝ -> ℝ
cosℝ a = sinℝ (a +ℝ pi/2)

expℂ : ℂ -> ℂ
expℂ (a :+ b) = (expa  ×ℝ (cosℝ b)) :+ (expa ×ℝ (sinℝ b))
                      where expa = expℝ a

[|_|²] : ℂ -> ℝ
[| (a :+ b) |²] = (a ×ℝ a) +ℝ (b ×ℝ b)

record Rot : Set where
  field
    a : ℂ
    b : ℂ
    c : ℂ
    d : ℂ

_ℂ×Rot_ : ℂ -> Rot -> Rot
s ℂ×Rot r  = record { a = s ×ℂ (Rot.a r)
                    ; b = s ×ℂ (Rot.b r)
                    ; c = s ×ℂ (Rot.c r)
                    ; d = s ×ℂ (Rot.d r)
                    }

_⋆_ : Rot -> Rot -> Rot
r1 ⋆ r2 = record { a = ((Rot.a r1) ×ℂ (Rot.a r2)) +ℂ ((Rot.b r1) ×ℂ (Rot.c r2))
                 ; b = ((Rot.a r1) ×ℂ (Rot.b r2)) +ℂ ((Rot.b r1) ×ℂ (Rot.d r2)) 
                 ; c = ((Rot.c r1) ×ℂ (Rot.a r2)) +ℂ ((Rot.d r1) ×ℂ (Rot.c r2))
                 ; d = ((Rot.c r1) ×ℂ (Rot.b r2)) +ℂ ((Rot.d r1) ×ℂ (Rot.d r2))
                 }

id' : Rot
id' = record { a = oneℂ
             ; b = zeroℂ
             ; c = zeroℂ
             ; d = oneℂ
             }

x' : Rot
x' = record { a = zeroℂ
            ; b = oneℂ
            ; c = oneℂ
            ; d = zeroℂ
            }

had' : Rot
had' = ( oneℂ ÷ℂ (ℝ⟶ℂ sqrt2)) ℂ×Rot 
          record { a = oneℂ
                 ; b = oneℂ
                 ; c = oneℂ
                 ; d = zeroℂ -ℂ oneℂ
                 }

phase' : ℝ -> Rot
phase' r = record { a = oneℂ
                  ; b = zeroℂ
                  ; c = zeroℂ
                  ; d = expℂ (zeroℝ :+ r) 
                  }

_* : Rot ->  Rot
r * = record { a = conjugate (Rot.a r)
             ; b = conjugate (Rot.c r)
             ; c = conjugate (Rot.b r)
             ; d = conjugate (Rot.d r)
             } 

record _≣_ (r1 r2 : Rot) : Set where
  field
    a : Rot.a r1 ≡ Rot.a r2
    b : Rot.b r1 ≡ Rot.b r2
    c : Rot.c r1 ≡ Rot.c r2
    d : Rot.d r1 ≡ Rot.d r2

_** : (a : Rot) -> ((a *) *) ≣ a
r ** = record { a = 2conjugate
              ; b = 2conjugate
              ; c = 2conjugate
              ; d = 2conjugate
              }

Norm : (a : Rot) -> (b : Rot) -> Set
Norm a b = (a ⋆ b) ≣ id'

data Rotation : Set where
  Rotate : (Σ Rot (\r -> Norm r (r *))) -> Rotation

*helper'' : ∀{r} -> Norm (r *) ((r *) *) -> Norm (r *) r
*helper'' {r} p = record { a = trans (cong (\x -> (conjugate (Rot.a r)) ×ℂ x) (sym (_≣_.a (r **))) 
                                     ≡[ _+ℂ_ ]≡ 
                                     cong (\x -> (conjugate (Rot.c r)) ×ℂ x) (sym (_≣_.c (r **)))) 
                                     (_≣_.a p)
                         ; b = trans ((cong (\x -> (conjugate (Rot.a r)) ×ℂ x) (sym (_≣_.b (r **))) 
                                     ≡[ _+ℂ_ ]≡ 
                                     cong (\x -> (conjugate (Rot.c r)) ×ℂ x) (sym (_≣_.d (r **))))) (_≣_.b p)
                         ; c = trans ((cong (\x -> (conjugate (Rot.b r)) ×ℂ x) (sym (_≣_.a (r **))) 
                                     ≡[ _+ℂ_ ]≡ 
                                     cong (\x -> (conjugate (Rot.d r)) ×ℂ x) (sym (_≣_.c (r **))))) (_≣_.c p)
                         ; d = trans ((cong (\x -> (conjugate (Rot.b r)) ×ℂ x) (sym (_≣_.b (r **))) 
                                     ≡[ _+ℂ_ ]≡ 
                                     cong (\x -> (conjugate (Rot.d r)) ×ℂ x) (sym (_≣_.d (r **))))) (_≣_.d p)
                         }

postulate
  *helper' : ∀{r r'} -> Norm r r' -> Norm (r *) (r' *)


*helper : ∀{r} -> Norm r (r *) -> Norm (r *) r
*helper p = *helper'' (*helper' p)

_*' : Rotation -> Rotation
Rotate (r , p) *' = Rotate (r * , record { a = trans (cong (\x -> conjugate (Rot.a r) ×ℂ x) 2conjugate 
                                                      ≡[ _+ℂ_ ]≡ 
                                                      cong (\x -> conjugate (Rot.c r) ×ℂ x) 2conjugate) 
                                                     (_≣_.a (*helper p))
                                         ; b = trans (cong (\x -> conjugate (Rot.a r) ×ℂ x) 2conjugate 
                                                      ≡[ _+ℂ_ ]≡ 
                                                      cong (\x -> conjugate (Rot.c r) ×ℂ x) 2conjugate) 
                                                     (_≣_.b (*helper p))
                                         ; c = trans (cong (\x -> conjugate (Rot.b r) ×ℂ x) 2conjugate 
                                                      ≡[ _+ℂ_ ]≡ 
                                                      cong (\x -> conjugate (Rot.d r) ×ℂ x) 2conjugate) 
                                                     (_≣_.c (*helper p))
                                         ; d = trans (cong (\x -> conjugate (Rot.b r) ×ℂ x) 2conjugate 
                                                      ≡[ _+ℂ_ ]≡ 
                                                      cong (\x -> conjugate (Rot.d r) ×ℂ x) 2conjugate) 
                                                     (_≣_.d (*helper p))
                                         })


aa⁺ : ∀{x y : ℝ} -> (x :+ y) ×ℂ conjugate (x :+ y) ≡ (((x ×ℝ x) +ℝ (y ×ℝ y)) :+ zeroℝ)
aa⁺ {x} {y} = (refl ≡[ _+ℝ_ ]≡ trans (-ℝ≡ (trans com×ℝ (sym dist-×ℝ))) -ℝ-ℝ ) ≡:+≡ trans (trans (trans com×ℝ (sym dist-×ℝ) ≡[ _+ℝ_ ]≡ refl) com+ℝ) inv+-ℝ  

postulate
  silly : ∀{A} -> {a b : A} -> a ≡ b

idP : Norm id' (id' *)
idP = record { a = trans ( (trans 
                                  (one×ℝ ≡[ _+ℝ_ ]≡ trans (cong -ℝ (trans com×ℝ 
                                                                          zero×ℝ)) 
                                                          -zeroℝ)  
                                  zero+ℝ)  
                          ≡[ _+ℝ_ ]≡ trans (cong (\x -> (zeroℝ ×ℝ zeroℝ) +ℝ -ℝ (zeroℝ ×ℝ x) ) -zeroℝ) 
                                            inv+-ℝ ) 
                         
                         zero+ℝ 
                    ≡:+≡ trans (trans (trans (cong (\x -> oneℝ ×ℝ x) -zeroℝ) zero×ℝ ≡[ _+ℝ_ ]≡ trans com×ℝ zero×ℝ) zero+ℝ ≡[ _+ℝ_ ]≡ trans (trans com×ℝ zero×ℝ ≡[ _+ℝ_ ]≡ zero×ℝ) zero+ℝ) zero+ℝ
             ; b = silly ≡:+≡ silly
             ; c = silly ≡:+≡ silly
             ; d = silly ≡:+≡ silly
             }

postulate
  hadP : Norm had' (had' *)
  phaseP : (r : ℝ) -> Norm (phase' r) ((phase' r) *)

xP : Norm x' (x' *)
xP = record  { a = trans 
                    (trans 
                     (trans 
                      (zero×ℝ ≡[ _+ℝ_ ]≡ trans 
                       (cong -ℝ 
                        (trans com×ℝ 
                         (zero×ℝ
                         )
                        )
                       ) -zeroℝ
                      ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                      (one×ℝ ≡[ _+ℝ_ ]≡ trans 
                       (cong -ℝ 
                        (trans com×ℝ zero×ℝ
                        )
                       ) -zeroℝ
                      ) zero+ℝ
                     ) com+ℝ
                    ) zero+ℝ ≡:+≡ trans 
                    (trans 
                     (trans com×ℝ zero×ℝ ≡[ _+ℝ_ ]≡ zero×ℝ
                     ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                     (trans 
                      (trans com×ℝ one×ℝ
                      ) -zeroℝ ≡[ _+ℝ_ ]≡ one×ℝ
                     ) zero+ℝ
                    ) zero+ℝ
             ; b = trans 
                   (trans 
                    (one×ℝ ≡[ _+ℝ_ ]≡ trans 
                     (cong -ℝ 
                      (trans com×ℝ zero×ℝ
                      )
                     ) -zeroℝ
                    ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                    (zero×ℝ ≡[ _+ℝ_ ]≡ trans 
                     (cong -ℝ 
                      (trans com×ℝ zero×ℝ
                      )
                     ) -zeroℝ
                    ) zero+ℝ
                   ) zero+ℝ ≡:+≡ trans 
                   (trans 
                    (trans com×ℝ zero×ℝ ≡[ _+ℝ_ ]≡ one×ℝ
                    ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                    (trans 
                     (trans com×ℝ one×ℝ
                     ) -zeroℝ ≡[ _+ℝ_ ]≡ zero×ℝ
                    ) zero+ℝ
                   ) zero+ℝ
             ; c = trans 
                    (trans 
                     (zero×ℝ ≡[ _+ℝ_ ]≡ trans 
                      (cong -ℝ 
                       (trans com×ℝ zero×ℝ
                       )
                      ) -zeroℝ
                     ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                     (one×ℝ ≡[ _+ℝ_ ]≡ trans 
                      (cong -ℝ 
                       (trans com×ℝ zero×ℝ
                       )
                      ) -zeroℝ) zero+ℝ
                     ) zero+ℝ ≡:+≡ trans 
                     (trans 
                      (trans 
                       (trans com×ℝ one×ℝ
                      ) -zeroℝ ≡[ _+ℝ_ ]≡ zero×ℝ
                     ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                     (trans com×ℝ zero×ℝ ≡[ _+ℝ_ ]≡ one×ℝ
                     ) zero+ℝ
                    ) zero+ℝ
             ; d = trans 
                    (trans 
                     (one×ℝ ≡[ _+ℝ_ ]≡ trans 
                      (cong -ℝ 
                       (trans com×ℝ zero×ℝ
                       )
                      ) -zeroℝ
                     ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                     (zero×ℝ ≡[ _+ℝ_ ]≡ trans 
                      (cong -ℝ 
                       (trans com×ℝ zero×ℝ
                       )
                      ) -zeroℝ
                     ) zero+ℝ
                    ) zero+ℝ ≡:+≡ trans 
                    (trans 
                     (trans 
                      (trans com×ℝ one×ℝ
                      ) -zeroℝ ≡[ _+ℝ_ ]≡ one×ℝ
                     ) zero+ℝ ≡[ _+ℝ_ ]≡ trans 
                     (trans com×ℝ zero×ℝ ≡[ _+ℝ_ ]≡ zero×ℝ
                     ) zero+ℝ
                    ) zero+ℝ
             }



id : Rotation
id = Rotate (id' , idP)

x : Rotation
x = Rotate (x' , xP)

had : Rotation
had = Rotate (had' , hadP)

phase : ℝ -> Rotation
phase r = Rotate (phase' r , phaseP r)


--other rotations?