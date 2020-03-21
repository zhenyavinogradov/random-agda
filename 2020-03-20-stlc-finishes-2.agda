module _ where

record ⊤ : Set where
  constructor tt

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

infixr 5 _,_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

data Bool : Set where
  false true : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

{-
Fin0
- (empty)

Fin1
- fin : (Fin0 → Bool) → Fin1
- nex : Fin1 → Fin1

Fin2
- fin : (Fin1 → Bool) → Fin2
- nex : Fin2 → Fin2
-}

module M1 where
  data Fin : ℕ → Set where
    fin : {n : ℕ} → (Fin n → Bool) → Fin (succ n)
    nex : {n : ℕ} → Fin (succ n) → Fin (succ n)
  
  induct : Set → (Set → Set) → (ℕ → Set)
  induct X F zero = X
  induct X F (succ n) = F (induct X F n)
  
  data Fin0 : Set where
  
  data FinF (X : Set) : Set where
    fin : (X → Bool) → FinF X
    nex : FinF X → FinF X
  
  Fin* : ℕ → Set
  Fin* = induct Fin0 FinF
    
  FinI : ℕ → Set
  FinI zero = Fin0
  FinI (succ n) = FinF (FinI n)

data Type : Set where
  _⇒_ : Type → Type → Type
  bool : Type

data Fin : Type → Set where
  fin-⇒ : {ρ τ : Type} → (Fin ρ → Fin τ) → Fin (ρ ⇒ τ)
  fin-bool : Fin bool
  nex : {τ : Type} → Fin τ → Fin τ

data Fin-bool : Set where
  fin-bool : Fin-bool
  nex : Fin-bool → Fin-bool
