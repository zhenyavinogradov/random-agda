{-# OPTIONS --type-in-type #-}
module _ where

data ⊥ : Set where

record ⊤ : Set where

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B
open _×_ public

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data List (A : Set) : Set where
  ε : List A
  _,_ : A → List A → List A

{-# NO_POSITIVITY_CHECK #-}
data Free (F : Set → Set) (A : Set) : Set where
  pure : A → Free F A
  roll : F (Free F A) → Free F A

{-# NO_POSITIVITY_CHECK #-}
record Cofree (F : Set → Set) (A : Set) : Set where
  coinductive
  field
    head : A
    tail : F (Cofree F A)

-- μX. (c : C) → R c × X
record Res (C : Set) (R : C → Set) : Set where
  inductive
  field
    res : (c : C) → R c × Res C R
open Res public

-- νX. (c : C) × (R c → X)
record Req (C : Set) (R : C → Set) : Set where
  coinductive
  field
    cmd : C
    cont : R cmd → Req C R
open Req public

μRes : (C : Set) → (R : C → Set) → Set
μRes C R = Res C R

FunctorRes : (C : Set → Set) → (R : (A : Set) → C A → Set) → (Set → Set)
FunctorRes C R A = Res (C A) (R A)

module _ (C : Set → Set) (R : (A : Set) → C A → Set) where
  map : ∀ {X Y} → (X → Y) → FunctorRes C R X → FunctorRes C R Y
  res (map f r) c = {!res r (f!}

FreeRes : (C : Set → Set) (R : (A : Set) → C A → Set) → (Set → Set)
FreeRes C R A = Res (Maybe (C A)) (maybe A (R A))
  where
    maybe : {X C : Set} → C → (X → C) → (Maybe X → C)
    maybe c f nothing = c
    maybe c f (just x) = f x
