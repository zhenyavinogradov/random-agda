module _ where

module _ where
  _€_ : {A B : Set} → A → (A → B) → B
  x € f = f x

  record ⊤ : Set where
    constructor tt

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (succ n)
    succ : {n : ℕ} → Fin n → Fin (succ n)

  data Vector (A : Set) : ℕ → Set where
    ε : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  data AllV {A : Set} (P : A → Set) : {n : ℕ} → Vector A n → Set where
    ε : AllV P ε
    _∷_ : {n : ℕ} {a : A} {as : Vector A n} → P a → AllV P as → AllV P (a ∷ as)

data Type : Set where
  -- π σ : List Type → Type
  _⇒_ : Type → Type → Type
  Nat : Type

Var : Set
Var = ℕ

Abs : Set → Set
Abs T = Var × T

data Term : Set where
  var : (τ : Type) → Var → Term

{-
  π-intr : (n : ℕ) → (τs : Vector Type n) → (Ms : Vector Term{-τᵢ-} n) → Term{-π τs-}
  π-elim : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-π τs-} → Term{-τᵢ-}

  σ-intr : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-τᵢ-} → Term{-σ τs-}
  σ-elim : (n : ℕ) → (τs : Vector Type n) → (ρ : Type) → (Ms : Vector (Abs Term{-τᵢ⊢ρ-}) n) → Term{-σ τs-} → Term{-ρ-}
  -}

  ⇒-intr : (ρ τ : Type) → (x : Var) → Term{-x:ρ⊢τ-} → Term{-ρ⇒τ-}
  ⇒-elim : (ρ τ : Type) → Term{-ρ-} → Term{-ρ⇒τ-} → Term{-τ-}

  Nzero : Term{-ℕ-}
  Nsucc : Term{-ℕ-} → Term{-ℕ-}
  Ncase : (ρ : Type) → Term{-ρ-} → (x : Var) → Term{-x:ρ⊢ρ-} → Term{-ℕ-} → Term{-ρ-}

Context : Set
Context = List (Var × Type)

data Has : Context → Var → Type → Set where
  here : ∀ {Γ x τ} → Has ((x , τ) ∷ Γ) x τ
  there : ∀ {Γ x τ p} → Has Γ x τ → Has (p ∷ Γ) x τ

data Valid : Context → Type → Term → Set where
  #var : ∀ {Γ} → (x : Var) → (τ : Type) → (h : Has Γ x τ) → Valid Γ τ (var τ x)

{-
  #π-intr : ∀ {Γ} → (n : ℕ) → (τs : Vector Type n) → (Ms : Vector Term{-τᵢ-} n) → AllV (Valid Γ {!!}
  #π-elim : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-π τs-} → Term{-τᵢ-} → {!!}

  #σ-intr : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-τᵢ-} → Term{-σ τs-} → {!!}
  #σ-elim : (n : ℕ) → (τs : Vector Type n) → (ρ : Type) → (Ms : Vector (Abs Term{-τᵢ⊢ρ-}) n) → Term{-σ τs-} → Term{-ρ-} → {!!}
  -}

  #⇒-intr : ∀ {Γ} → (ρ τ : Type) → (x : Var) → (M : Term{-x:ρ⊢τ-}) → Valid ((x , ρ) ∷ Γ) τ M → Valid Γ (ρ ⇒ τ) (⇒-intr ρ τ x M)
  #⇒-elim : ∀ {Γ} → (ρ τ : Type) → (N : Term{-ρ-}) → (M : Term{-ρ⇒τ-}) → Valid Γ ρ N → Valid Γ (ρ ⇒ τ) M → Valid Γ τ (⇒-elim ρ τ N M)

  #Nzero : ∀ {Γ} → Valid Γ Nat Nzero
  #Nsucc : ∀ {Γ} → (M : Term{-ℕ-}) → Valid Γ Nat M → Valid Γ Nat (Nsucc M)
  #Ncase : ∀ {Γ} → (ρ : Type) → (N₀ : Term{-ρ-}) → (x : Var) → (Nₛ : Term{-x:ρ⊢ρ-}) → (M : Term{-ℕ-})
         → Valid Γ ρ N₀ → Valid ((x , ρ) ∷ Γ) ρ Nₛ → Valid Γ Nat M → Valid Γ ρ (Ncase ρ N₀ x Nₛ M)

TypeVal : Type → Set
TypeVal (ρ ⇒ τ) = TypeVal ρ → TypeVal τ
TypeVal Nat = ℕ

ContextVal : Context → Set
ContextVal ε = ⊤
ContextVal ((_ , τ) ∷ Γ) = TypeVal τ × ContextVal Γ

ℕcase : {X : Set} → (n : ℕ) → X → (X → X) → X
ℕcase zero f₀ fₛ = f₀
ℕcase (succ n) f₀ fₛ = fₛ (ℕcase n f₀ fₛ)

TermVal : (Γ : Context) → (τ : Type) → (M : Term) → Valid Γ τ M → ContextVal Γ → TypeVal τ
TermVal _ _ .(var τ x) (#var x τ here) (vτ , vΓ) = vτ
TermVal _ _ .(var τ x) (#var x τ (there h)) (_ , vΓ) = TermVal _ _ (var τ x) (#var x τ h) vΓ
TermVal Γ .(ρ ⇒ τ) .(⇒-intr ρ τ x M) (#⇒-intr ρ τ x M #M) vΓ = \vx → TermVal _ _ M #M (vx , vΓ)
TermVal Γ τ .(⇒-elim ρ τ N M) (#⇒-elim ρ .τ N M #N #M) vΓ =  (TermVal _ _ M #M vΓ) (TermVal _ _ N #N vΓ)
TermVal Γ .Nat .Nzero #Nzero vΓ = zero
TermVal Γ .Nat .(Nsucc M) (#Nsucc M #M) vΓ = succ (TermVal _ _ M #M vΓ)
TermVal Γ τ .(Ncase τ N₀ x Nₛ M) (#Ncase .τ N₀ x Nₛ M #N₀ #Nₛ #M) vΓ = ℕcase (TermVal _ _ M #M vΓ) (TermVal _ _ N₀ #N₀ vΓ) (\vτ → TermVal _ _ Nₛ #Nₛ (vτ , vΓ) )

bla : {!!}
bla = TermVal ε Nat (Ncase Nat Nzero 91 (Nsucc (Nsucc (var Nat 91))) (Nsucc (Nsucc Nzero))) (#Ncase Nat Nzero 91 (Nsucc (Nsucc (var Nat 91))) (Nsucc (Nsucc Nzero)) #Nzero (#Nsucc (Nsucc (var Nat 91)) (#Nsucc (var Nat 91) (#var 91 Nat here))) (#Nsucc (Nsucc Nzero) (#Nsucc Nzero #Nzero))) tt

blaa : {!!}
blaa = {!bla!}
