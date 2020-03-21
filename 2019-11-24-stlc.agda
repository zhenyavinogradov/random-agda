module _ where

module _ where
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

Var : Set
Var = ℕ

data Type : Set where
  σ π : List Type → Type
  μ ν : (t : Var) → Type → Type
  _⇒_ : Type → Type → Type
  --∀̂ ∃̂ : (t : Var) → Type → Type

Abs : Set → Set
Abs T = Var × T

data Term : Set where
  var : Var → Term

  π-intr : (τs : List Type) → (Ms : List Term) → Term
  π-elim : (τs : List Type) → (i : ℕ) → Term → Term
  
  σ-intr : (τs : List Type) → (i : ℕ) → Term → Term
  σ-elim : (τs : List Type) → (ρ : Type) → (Ms : List (Abs Term)) → Term → Term

  ⇒-intr : (ρ τ : Type) → Abs Term → Term
  ⇒-elim : (ρ τ : Type) → Term → Term → Term

  μ-intr : (ϕ : Type) → Term {- ϕ # μ ϕ -} → Term {- μ ϕ -}
  μ-elim : (ϕ : Type) → (ρ : Type) → Abs Term {- ϕ # ρ → ρ -} → Term {- μ ϕ -} → Term {- ρ -}

  ν-intr : (ϕ : Type) → (ρ : Type) → Abs Term {- ρ → ϕ # ρ -} → Term {- ρ -} → Term {- ν ϕ -}
  ν-elim : (ϕ : Type) → Term {- ν ϕ -} → Term {- ϕ # ν ϕ -}

  {-
  ∀-intr : (τ : Type) → Term {- [α∷αs] τ -} → Term {- [αs] ∀α.τ -}
  ∀-elim : (τ : Type) → Term {- [αs] ∀α.τ -} → Term {- [αs] τ[α:=ρ] -}

  ∃-intr : (τ : Type) → Term {- [αs] τ[α:=ρ] -} → Term {- [αs] ∃α.τ -}
  ∃-elim : (τ : Type) → Term {- [αs] ∃α.τ -} → Term {- [α∷αs] ρ -} → Term {- [αs] ρ -}
  -}
