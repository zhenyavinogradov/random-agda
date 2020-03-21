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


data Type : Set where
  _⇒_ : Type → Type → Type
  Nat : Type

Context : Set
Context = List Type

data Term : Set where
  var : (i : ℕ) → Term

  ⇒-intr : (ρ τ : Type) → Term → Term
  ⇒-elim : (ρ τ : Type) → Term → Term → Term

  N-elim : (ρ : Type) → Term {-ρ-} → Term {-ρ-} → Term {-ℕ-} → Term {-ρ-}
  N-zero : Term {-ℕ-}
  N-succ : Term {-ℕ-} → Term {-ℕ-}

data Has : (Γ : Context) → ℕ → Type → Set where
  here : ∀ {Γ τ} → Has (τ ∷ Γ) zero τ
  there : ∀ {Γ i τ p} → Has Γ i τ → Has (p ∷ Γ) (succ i) τ

data Valid : Context → Type → Term → Set where
  #var : ∀ {Γ} → (i : ℕ) → (τ : Type) → (h : Has Γ i τ) → Valid Γ τ (var i)

  #⇒-intr : ∀ {Γ} → (ρ τ : Type) → (M : Term {-τ-}) → Valid (ρ ∷ Γ) τ M → Valid Γ (ρ ⇒ τ) (⇒-intr ρ τ M)
  #⇒-elim : ∀ {Γ} → (ρ τ : Type)
          → (N : Term {-ρ-}) → (#N : Valid Γ ρ N)
          → (M : Term {-ρ⇒τ-}) → (#M : Valid Γ (ρ ⇒ τ) M)
          → Valid Γ τ (⇒-elim ρ τ N M)

  #N-zero : ∀ {Γ} → Valid Γ Nat N-zero
  #N-succ : ∀ {Γ} → (M : Term {-ℕ-}) → Valid Γ Nat M → Valid Γ Nat (N-succ M)
  #N-elim : ∀ {Γ} → (ρ : Type)
         → (N₀ : Term {-ρ-}) → Valid Γ ρ N₀
         → (Nₛ : Term {-ρ-}) → Valid (ρ ∷ Γ) ρ Nₛ
         → (M : Term {-ℕ-}) → Valid Γ Nat M
         → Valid Γ ρ (N-elim ρ N₀ Nₛ M)

data Coterm : Set where
  nil : Coterm
  _·_ : Term → Coterm → Coterm

Machine : Set
Machine = Term × Coterm

data Step : Machine → Machine → Set where
  ⇒-step : ∀ {ρ τ N M γ} → Step (⇒-elim ρ τ N (⇒-intr ρ τ M) , γ) {!M , N · ?!}
