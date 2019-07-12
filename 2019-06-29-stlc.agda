-- stlc with induction and coinduction
module _ where

module _ where
  module _ where
    record ⊤ : Set where
      constructor tt

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    data List (A : Set) : Set where
      ε : List A
      _∷_ : A → List A → List A

  -- list
  module _ where
    data Elem {A : Set} : List A → A → Set where
      here : ∀ {a as} → Elem (a ∷ as) a
      there : ∀ {a a' as} → Elem as a → Elem (a' ∷ as) a

    data All {A : Set} (P : A → Set) : List A → Set where
      ε : All P ε
      _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

    get : ∀ {A : Set} {P : A → Set} {τs τ} → All P τs → Elem τs τ → P τ
    get = {!!}

module _ where
  data Type : Set → Set where
    var  : ∀ {Θ} → Θ → Type Θ
    σ π  : ∀ {Θ} → List (Type Θ) → Type Θ
    μ ν  : ∀ {Θ} → Type (⊤ + Θ) → Type Θ

  tbind : ∀ {A B} → Type A → (A → Type B) → Type B
  tbind = {!!}

  tbinda : ∀ {A B} → Type (A + B) → (A → Type B) → Type B
  tbinda = {!!}

  _#_ : ∀ {Θ} → Type (⊤ + Θ) → Type Θ → Type Θ
  ϕ # τ = tbinda ϕ (\_ → τ)

  Ctx : Set → Set
  Ctx Θ = List (Type Θ)

  {-
  Type : Set
  _⇒_ : Type → Type → Set
  _⇛_ : (A ⇒ B) → (A ⇒ B) → Set
  
  _∘_ : (σ ⇒ τ) → (ρ ⇒ σ) → (ρ ⇒ τ)
  
  π : List Type → Type
  prj : Elem τs τ → (π τs ⇒ τ)
  com : All (\τ → ρ ⇒ τ) τs → (ρ ⇒ π τs)
  π-rule : prj i ∘ com As ⇛ get As i
  
  σ : List Type → Type
  inj : Elem τs τ → (τ ⇒ σ τs)
  sum : All (\τ → τ ⇒ ρ) τs → (σ τs ⇒ ρ)
  σ-rule : sum As ∘ inj i ⇛ get As i
  -}
  data Term {Θ : Set} : Ctx Θ → Type Θ → Type Θ → Set where
    _∘_ : ∀ {Γ σ τ ρ} → Term Γ τ ρ → Term Γ σ τ → Term Γ σ ρ
    id : ∀ {Γ} τ → Term Γ τ τ

    var : ∀ {Γ σ τ} → Elem Γ τ → Term Γ σ τ

    ctx : ∀ {Γ Δ σ τ} → Term Δ σ τ → All (\ρ → Term Γ σ ρ) Δ → Term Γ σ τ

    inj : ∀ {Γ τs τ} → Elem τs τ → Term Γ τ (σ τs)
    sum : ∀ {Γ τs ρ} → All (\τ → Term Γ τ ρ) τs → Term Γ (σ τs) ρ

    prj : ∀ {Γ τs τ} → Elem τs τ → Term Γ (π τs) τ
    com : ∀ {Γ τs ρ} → All (\τ → Term Γ ρ τ) τs → Term Γ ρ (π τs)

    con : ∀ {Γ ϕ} → Term Γ (ϕ # μ ϕ) (μ ϕ)
    ind : ∀ {Γ ρ} ϕ → Term Γ (ϕ # ρ) ρ → Term Γ (μ ϕ) ρ

    dec : ∀ {Γ ϕ} → Term Γ (ν ϕ) (ϕ # ν ϕ)
    coi : ∀ {Γ ρ} ϕ → Term Γ ρ (ϕ # ρ) → Term Γ ρ (ν ϕ)

  map : ∀ {Θ} → (ϕ : Type (⊤ + Θ)) → ∀ {Γ σ τ} → Term Γ σ τ → Term Γ (ϕ # σ) (ϕ # τ)
  map = {!!}

  infix 5 _⇒_
  data _⇒_ {Θ : Set} {Γ : Ctx Θ} : ∀ {σ τ : Type Θ} → Term Γ σ τ → Term Γ σ τ → Set where
    id-l : ∀ {σ τ} → (A : Term Γ σ τ) → A ∘ id σ ⇒ A
    id-r : ∀ {σ τ} → (A : Term Γ σ τ) → id τ ∘ A ⇒ A

    sum-rule : ∀ {τ ρ τs} {As : All (\α → Term Γ α ρ) τs} {i : Elem τs τ} → sum As ∘ inj i ⇒ get As i
    product-rule : ∀ {τ ρ τs} {As : All (\α → Term Γ ρ α) τs} {i : Elem τs τ} → prj i ∘ com As ⇒ get As i
    induction : {ϕ : Type (⊤ + Θ)} {ρ : Type Θ} {f : Term Γ (ϕ # ρ) ρ} → ind ϕ f ∘ con ⇒ f ∘ map ϕ (ind ϕ f)
    coinduction : {ϕ : Type (⊤ + Θ)} {ρ : Type Θ} {f : Term Γ ρ (ϕ # ρ)} → dec ∘ coi ϕ f ⇒ map ϕ (coi ϕ f) ∘ f
