module _ where

module _ where
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,,_
    field
      fst% : A
      snd% : B fst%
  open Σ public

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data Elem {A : Set} : List A → Set where
    here : ∀ {a as} → Elem (a ∷ as)
    there : ∀ {a as} → Elem as → Elem (a ∷ as)

  get : {A : Set} → (as : List A) → Elem as → A
  get (a ∷ as) here = a
  get (a ∷ as) (there i) = get as i

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : {a : A} {as : List A} → P a → All P as → All P (a ∷ as)

data Var : Set where
  $_ : ℕ → Var

data Type : (Δ : List Var) → Set where
  var : ∀ {Δ} → Var → Type Δ
  σ π : ∀ {Δ} → List (Type Δ) → Type Δ
  _⇒_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  μ ν : ∀ {Δ} → Type Δ → Type Δ
  ∀̃ ∃̃ : ∀ {Δ} → Type Δ → Type Δ

data Positive : (Δ : List Var) → Var → Type Δ → Set where

AbsT : {S : Set} → (T : List (Var × S) → S → Set) → (List (Var × S) → S → S → Set)
AbsT T Γ ρ τ = Σ Var \x → T ((x , ρ) ∷ Γ) τ

data Term {Δ : List Var} : (Γ : List (Var × Type Δ)) → (τ : Type Δ) → Set where
  var : ∀ {Γ τ} → Var → Term Γ τ

  σ-intr : ∀ {Γ} → (τs : List (Type Δ)) (i : Elem τs) → Term Γ (get τs i) → Term Γ (σ τs)
  σ-elim : ∀ {Γ} → (τs : List (Type Δ)) (ρ : Type Δ) → All (\τ → AbsT Term Γ τ ρ) τs → Term Γ (σ τs) → Term Γ ρ

  π-intr : ∀ {Γ} → (τs : List (Type Δ)) (ρ : Type Δ) → All (\τ → Term Γ τ) τs → Term Γ (π τs)
  π-elim : ∀ {Γ} → (τs : List (Type Δ)) (i : Elem τs) → Term Γ (π τs) → Term Γ (get τs i)

  ⇒-intr : ∀ {Γ} → (ρ τ : Type Δ) → AbsT Term Γ ρ τ → Term Γ (ρ ⇒ τ)
  ⇒-elim : ∀ {Γ} → (ρ τ : Type Δ) → Term Γ ρ → Term Γ (ρ ⇒ τ) → Term Γ τ

data Type₁ {Δ : List Var} : (Γ : List (Var × Type Δ)) → (Δ₁ : List Var) → Set where
  var : ∀ {Γ Δ₁} → Var → Type₁ Γ Δ₁
  σ₁ π₁ : ∀ {Γ Δ₁} → List (Type₁ Γ Δ₁) → Type₁ Γ Δ₁
  _⇒₁_ : ∀ {Γ Δ₁} → Type₁ Γ Δ₁ → Type₁ Γ Δ₁ → Type₁ Γ Δ₁

  Σ̂ Π̂ : ∀ {Γ Δ₁} → ∀ x A → Type₁ ((x , A) ∷ Γ) Δ₁ → Type₁ Γ Δ₁

data Term₁ {Δ : List Var} {Δ₁ : List Var} : (Γ : List (Var × Type Δ)) (Γ₁ : List (Var × Type₁ Γ Δ₁)) → (P : Type₁ Γ Δ₁) → Set where
  var : ∀ {Γ Γ₁ P} → Var → Term₁ Γ Γ₁ P

  σ-intr : ∀ {Γ Γ₁} → (Ps : List (Type₁ Γ Δ₁)) (i : Elem Ps) → Term₁ Γ Γ₁ (get Ps i) → Term₁ Γ Γ₁ (σ₁ Ps)
  σ-elim : ∀ {Γ Γ₁} → (Ps : List (Type₁ Γ Δ₁)) (R : Type₁ Γ Δ₁) → All (\P → AbsT (Term₁ Γ) Γ₁ P R) Ps → Term₁ Γ Γ₁ (σ₁ Ps) → Term₁ Γ Γ₁ R

  π-intr : ∀ {Γ Γ₁} → (Ps : List (Type₁ Γ Δ₁)) (ρ : Type₁ Γ Δ₁) → All (\P → Term₁ Γ Γ₁ P) Ps → Term₁ Γ Γ₁ (π₁ Ps)
  π-elim : ∀ {Γ Γ₁} → (Ps : List (Type₁ Γ Δ₁)) (i : Elem Ps) → Term₁ Γ Γ₁ (π₁ Ps) → Term₁ Γ Γ₁ (get Ps i)

  ⇒-intr : ∀ {Γ Γ₁} → (R P : Type₁ Γ Δ₁) → AbsT (Term₁ Γ) Γ₁ R P → Term₁ Γ Γ₁ (R ⇒₁ P)
  ⇒-elim : ∀ {Γ Γ₁} → (R P : Type₁ Γ Δ₁) → Term₁ Γ Γ₁ R → Term₁ Γ Γ₁ (R ⇒₁ P) → Term₁ Γ Γ₁ P

  Π-intr : ∀ {Γ Γ₁} → (z x : Var) (A : Type Δ) (P : Type₁ ((z , A) ∷ Γ) Δ₁) → Term₁ ((x , A) ∷ Γ) {!Γ₁!} {!P[z:=x]!} → Term₁ Γ Γ₁ (Π̂ z A P)
  Π-elim : ∀ {Γ Γ₁} → (z : Var) (A : Type Δ) (P : Type₁ ((z , A) ∷ Γ) Δ₁) → (M : Term Γ A) → Term₁ Γ Γ₁ (Π̂ z A P) → Term₁ Γ Γ₁ {!P[z:=M]!}

  Σ-intr : ∀ {Γ Γ₁} → (z : Var) (A : Type Δ) (P : Type₁ ((z , A) ∷ Γ) Δ₁) → (M : Term Γ A) → Term₁ Γ Γ₁ {!P[z:=M]!} → Term₁ Γ Γ₁ (Σ̂ z A P)
  Σ-elim : ∀ {Γ Γ₁} → (z x S : Var) (A : Type Δ) (P : Type₁ ((z , A) ∷ Γ) Δ₁) (R : Type₁ Γ Δ₁)
         → Term₁ ((x , A) ∷ Γ) ((S , {!P[z:=x]!}) ∷ {!Γ₁!}) {!R!} → Term₁ Γ Γ₁ (Σ̂ z A P) → Term₁ Γ Γ₁ R
