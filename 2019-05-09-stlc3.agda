-- simple type theory with (co)products and (co)induction, aiming for simpler term construction
-- awkward to define reduction relation
module Stlc3 where

-- lib
module _ where
  -- natural
  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

  -- list
  module _ where
    infixr 10 _,_
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

    data _∈_ {A : Set} : A → List A → Set where
      here : ∀ {a as} → a ∈ (a , as)
      there : ∀ {a a' as} → a ∈ as → a ∈ (a' , as)

    data All {A : Set} : List A → (A → Set) → Set where
      ε : ∀ {P} → All ε P
      _,_ : ∀ {P a as} → P a → All as P → All (a , as) P

    get : {A : Set} {P : A → Set} {a : A} {as : List A} → All as P → a ∈ as → P a
    get (p , ps) here = p
    get (p , ps) (there i) = get ps i

  -- fin
  module _ where
    data Fin : ℕ → Set where
      zero : ∀ {n} → Fin (succ n)
      succ : ∀ {n} → Fin n → Fin (succ n)

TCtx : Set
TCtx = ℕ

data Type : (Δ : TCtx) → Set where
  var : ∀ {Δ} → Fin Δ → Type Δ
  -- !_ : ∀ {Δ} → Type (succ Δ) → Type Δ
  σ π : ∀ {Δ} → List (Type Δ) → Type Δ
  μ ν : ∀ {Δ} → Type (succ Δ) → Type Δ

infixr 15 _#_
_#_ : ∀ {Δ} → Type (succ Δ) → Type Δ → Type Δ
τ # ρ = {!!}

!_ : ∀ {Δ} → Type Δ → Type (succ Δ)
!_ = {!!}

!!_ : ∀ {Δ} → Type zero → Type Δ
!!_ = {!!}

Ctx : TCtx → Set
Ctx Δ = List (Type Δ)

infix 5 _⊢_
{-# NO_POSITIVITY_CHECK #-}
data _⊢_ {Δ : TCtx} : Ctx Δ → Type Δ → Set where
  ctx : ∀ {Γ τ} → τ ∈ Γ → Γ ⊢ τ
  cmp : ∀ {Γ Σ τ} → All Σ (\α → Γ ⊢ α) → Σ ⊢ τ → Γ ⊢ τ

  σ-intr : ∀ {Γ τ τs} → τ ∈ τs → Γ ⊢ τ → Γ ⊢ σ τs
  σ-elim : ∀ {Γ τs ρ} → Γ ⊢ σ τs → All τs (\τ → τ , Γ ⊢ ρ) → Γ ⊢ ρ

  π-intr : ∀ {Γ τs} → All τs (\τ → Γ ⊢ τ) → Γ ⊢ π τs
  π-elim : ∀ {Γ τ τs} → τ ∈ τs → Γ ⊢ π τs → Γ ⊢ τ

  μ-intr : ∀ {Γ τ} → Γ ⊢ τ # μ τ → Γ ⊢ μ τ
  μ-elim : ∀ {Γ τ ρ} → Γ ⊢ μ τ → τ # ρ , Γ ⊢ ρ → Γ ⊢ ρ

  ν-intr : ∀ {Γ τ ρ} → Γ ⊢ ρ → ρ , Γ ⊢ τ # ρ → Γ ⊢ ν τ
  ν-elim : ∀ {Γ τ} → Γ ⊢ ν τ → Γ ⊢ τ # ν τ

-- evaluation
module _ {Δ : TCtx} (evalTV : Fin Δ → Set) where
  evalType : Type Δ → Set
  evalType = {!!}

  eval : {Γ : Ctx Δ} {τ : Type Δ} → Γ ⊢ τ → All Γ (\α → evalType α) → evalType τ
  eval (ctx i) c = get c i
  eval (cmp r f) c = {!!}
  eval (σ-intr x f) c = {!!}
  eval (σ-elim f x) c = {!!}
  eval (π-intr x) c = {!!}
  eval (π-elim x f) c = {!!}
  eval (μ-intr f) c = {!!}
  eval (μ-elim f f₁) c = {!!}
  eval (ν-intr f f₁) c = {!!}
  eval (ν-elim f) c = {!!}

module _ where
  ignoreContext : ∀ {Δ} {Γ : Ctx Δ} {τ : Type Δ} → ε ⊢ τ → Γ ⊢ τ
  ignoreContext f = cmp ε f

{-# NO_POSITIVITY_CHECK #-}
data _⇒_ {Δ : TCtx} : {Γ : Ctx Δ} {τ : Type Δ} → (f g : Γ ⊢ τ) → Set where


module _ where
  var0 : ∀ {Δ} → Type (succ Δ)
  var0 = var zero

module _ where
  module _ where
    t⊤ : Type zero
    t⊤ = π ε

    e⊤ : ε ⊢ t⊤
    e⊤ = π-intr ε

  module _ where
    tBool : Type zero
    tBool = σ (t⊤ , t⊤ , ε)

    eFalse : ε ⊢ tBool
    eFalse = σ-intr here e⊤

    eTrue : ε ⊢ tBool
    eTrue = σ-intr (there here) e⊤

  module _ where
    tPair : ∀ {Δ} → Type Δ → Type Δ → Type Δ
    tPair τ₁ τ₂ = π (τ₁ , τ₂ , ε)

    ePair : ∀ {Δ} {τ₁ τ₂ : Type Δ} {Γ} → Γ ⊢ τ₁ → Γ ⊢ τ₂ → Γ ⊢ tPair τ₁ τ₂
    ePair f g = π-intr (f , g , ε)

  module _ where
    tEither : ∀ {Δ} → Type Δ → Type Δ → Type Δ
    tEither τ₁ τ₂ = σ (τ₁ , τ₂ , ε)

  module _ where
    tℕ : Type zero
    tℕ = μ (σ (π ε , var0 , ε))

    eSucc : tℕ , ε ⊢ tℕ
    eSucc = μ-intr {!!}

    eAdd : tℕ , tℕ , ε ⊢ tℕ
    eAdd = μ-elim (ctx here) (σ-elim (ctx here) (ctx (there here) , cmp (ctx here , ε) eSucc , ε))

  module _ where
    tList : ∀ {Δ} → Type Δ → Type Δ
    tList τ = μ (tEither (!! t⊤) (tPair (! τ) var0))

  module _ where
    tColist : ∀ {Δ} → Type Δ → Type Δ
    tColist τ = ν (tEither (!! t⊤) (tPair (! τ) var0))

  module _ where
    tDelay : ∀ {Δ} → Type Δ → Type Δ
    tDelay τ = ν (tEither (! τ) var0)

  module _ where
    tString : Type zero
    tString = {!!}

  module _ where
    tStream : ∀ {Δ} → Type Δ → Type Δ
    tStream τ = ν (tPair (! τ) var0)

    eShowStream : ∀ {Δ} {τ : Type Δ} → τ , ε ⊢ !! tDelay tString → tStream τ , ε ⊢ !! tDelay tString
    eShowStream sh = {!!}

s1 : ε ⊢ tStream tBool
s1 = ν-intr {ρ = t⊤} e⊤ {!ePair (ignoreContext eFalse) e⊤!}

s2 : ε ⊢ tStream tBool
s2 = ν-intr {ρ = tBool} eFalse {!ePair (ignoreContext eFalse) eTrue!}
