-- 2019-05-12, real analysis algebraically: streams of embedded rational intervals
module Analysis where

-- lib
module _ where
  -- pair
  module _ where
    record _×_ (A B : Set) : Set where
      field
        fst : A
        snd : B

  -- endorelation
  module _ where
    Rel : Set → Set₁
    Rel A = A → A → Set
    
    data mapRel {A B : Set} (f : A → B) (R : Rel A) : Rel B where
      mkMapRel : {a a' : A} → R a a' → mapRel f R (f a) (f a')
    
    _≤_ : {A : Set} → Rel A → Rel A → Set
    _≤_ {A} R S = (a a' : A) → R a a' → S a a'
    
    Sub' : {A B : Set} → (A → B) → Rel A → Rel B → Set
    Sub' {A = A} f R S = (a a' : A) → R a a' → S (f a) (f a')

-- infinite R-chain starting from `head`
record Inf {A : Set} (R : Rel A) (head : A) : Set where
  coinductive
  constructor mkInf
  field
    next : A
    step : R head next
    cont : Inf R next
open Inf public

mapInf : {A B : Set} {R : Rel A} {a : A} → (f : A → B) → (Inf R a → Inf (mapRel f R) (f a))
next (mapInf f i) = f (next i)
step (mapInf f i) = mkMapRel (step i)
cont (mapInf f i) = mapInf f (cont i)

mapInf' : {A B : Set} {R : Rel A} {S : Rel B} {a : A} → (f : A → B) → (r : Sub' f R S) → (Inf R a → Inf S (f a))
next (mapInf' f r i) = f (next i)
step (mapInf' f r i) = r _ _ (step i)
cont (mapInf' f r i) = mapInf' f r (cont i)

mapInf'' : {A : Set} {R : Rel A} {a : A} → (f : A → A) → (r : Sub' f R R) → (Inf R a → Inf R (f a))
mapInf'' f r i = mapInf' f r i

-- eventually
data Ev {A : Set} {R : Rel A} : (a : A) → {s : A} → Inf R s → Set where
  here : ∀ {a s} {i : Inf R s} → R a s → Ev a i
  there : {a s s' : A} {g' : R s' s} {i : Inf R s} → Ev a i → Ev a (mkInf s g' i)

record Each {A : Set} {R : Rel A} {s : A} (i : Inf R s) (P : A → Set) : Set where
  coinductive
  field
    this : P s
    rest : Each {s = next i} (cont i) P

Subsumes : {A : Set} {R : Rel A} {s s' : A} → Inf R s → Inf R s' → Set
Subsumes i₁ i₂ = Each i₁ (\a → Ev a i₂)

Equivalent : {A : Set} {R : Rel A} {s s' : A} → Inf R s → Inf R s' → Set
Equivalent i₁ i₂ = Subsumes i₁ i₂ × Subsumes i₂ i₁

-- Function = (f : A → A, _ : R a a' → R (f a) (f a'))

-- sequenceLimit : Stream Real → Real
-- functionLimit : Function → Real → Real
-- differentiation : Function → Function
