-- stlc strong normalization
module _ where

-- lib
module _ where
  -- eq
  module _ where
    data _≡_ {A : Set} (a : A) : A → Set where
      refl : a ≡ a

  -- list
  module _ where
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

    _++_ : {A : Set} → List A → List A → List A
    ε ++ ys = ys
    (x , xs) ++ ys = x , (xs ++ ys)

    data All {A : Set} (P : A → Set) : List A → Set where
      ε : All P ε
      _,_ : ∀ {a as} → P a → All P as → All P (a , as)

    mapAll : ∀ {A} {P Q : A → Set} {as} → (f : ∀ {a} → P a → Q a) → (All P as → All Q as)
    mapAll f ε = ε
    mapAll f (Pa , Pas) = f Pa , mapAll f Pas

    all++ : ∀ {A} {P : A → Set} {bs} → (as : List A) → All P as → All P bs → All P (as ++ bs)
    all++ ε ε Pbs = Pbs
    all++ (a , as) (Pa , Pas) Pbs = Pa , all++ as Pas Pbs

    data _∈_ {A : Set} (a : A) : List A → Set where
      here : ∀ {as} → a ∈ (a , as)
      there : ∀ {a' as} → a ∈ as → a ∈ (a' , as)

    get : ∀ {A} {P : A → Set} {a as} → All P as → a ∈ as → P a
    get (Pa , Pas) here = Pa
    get (Pa , Pas) (there i) = get Pas i

    all : ∀ {A} {P : A → Set} {as} → (∀ {a} → a ∈ as → P a) → All P as
    all {as = ε} f = ε
    all {as = a , as} f = f here , all {as = as} (\i → f (there i))

    data All2 {A : Set} {P : A → Set} (P2 : {a : A} → P a → Set) : {as : List A} → (Pas : All P as) → Set where
      ε : All2 P2 ε
      _,_ : ∀ {a as} {Pa : P a} {Pas : All P as} → P2 Pa → All2 P2 Pas → All2 P2 (Pa , Pas)


module _ (Θ : Set) where
  data Type : Set where
    atom : Θ → Type
    _⇒_ : Type → Type → Type

  record EqBag {A : Set} (as bs : List A) : Set where
    field
      to : ∀ {a} → a ∈ as → a ∈ bs
      from : ∀ {a} → a ∈ bs → a ∈ as
      to∘from : ∀ {a} → (i : a ∈ bs) → to (from i) ≡ i
      from∘to : ∀ {a} → (i : a ∈ as) → from (to i) ≡ i
  open EqBag public

  data Lam : (Γ : List Type) → Type → Set where
    var : ∀ {Γ τ} → τ ∈ Γ → Lam Γ τ
    app : ∀ {Γ σ τ} → Lam Γ (σ ⇒ τ) → Lam Γ σ → Lam Γ τ
    lam : ∀ {Γ σ τ} → Lam (σ , Γ) τ → Lam Γ (σ ⇒ τ)

  mapLam : ∀ {Γ₁ Γ₂ τ} → (∀ {σ} → σ ∈ Γ₁ → σ ∈ Γ₂) → (Lam Γ₁ τ → Lam Γ₂ τ)
  mapLam f (var x) = var (f x)
  mapLam f (app e₁ e₂) = app (mapLam f e₁) (mapLam f e₂)
  mapLam f (lam e) = lam (mapLam (\{ here → here ; (there i) → there (f i) }) e)

  tLam : ∀ {Γ Γ' τ} → EqBag Γ Γ' → Lam Γ τ → Lam Γ' τ
  tLam eq e = mapLam (to eq) e

  Valuation : List Type → List Type → Set
  Valuation τs Γ = All (Lam Γ) τs

  bind : ∀ {Γ₁ Γ₂ τ} → Lam Γ₁ τ → Valuation Γ₁ Γ₂ → Lam Γ₂ τ
  bind (var x) f = get f x
  bind (app e₁ e₂) f = app (bind e₁ f) (bind e₂ f)
  bind (lam e) f = lam (bind e (var here , mapAll (mapLam there) f))

  bindp : ∀ {Γ₁ Γ₂ τ} → Lam (Γ₁ ++ Γ₂) τ → Valuation Γ₁ Γ₂ → Lam Γ₂ τ
  bindp {Γ₁ = Γ₁} e f = bind e (all++ Γ₁ f (all var))

  _*⇒_ : List Type → Type → Type
  ε *⇒ τ = τ
  (σ , σs) *⇒ τ = σ ⇒ (σs *⇒ τ)

  app* : ∀ {Γ σs τ} → Lam Γ (σs *⇒ τ) → All (Lam Γ) σs → Lam Γ τ
  app* e ε = e
  app* e (d , ds) = app* (app e d) ds

  SN : ∀ {Γ τ} → Lam Γ τ → Set
  SN = {!!}

  data Args (σs : List Type) (τ : Type) : Type → Set where
    args : Args σs τ (σs *⇒ τ)

  toArgs : ∀ {Γ σs τ τ'} → Args σs τ' τ → Lam Γ τ → Lam Γ (σs *⇒ τ')
  toArgs args e = e

  {-# NO_POSITIVITY_CHECK #-}
  record USN {Γ τ} (e : Lam Γ τ) : Set where
    field usn : ∀ {τ'} → (σs : List Type) → (r : Args σs τ' τ) → (es : All (Lam Γ) σs) → (usnes : All2 USN es) → SN (app* (toArgs r e) es)
  open USN public

  lem : ∀ {Γ τ} → (σs : List Type) → (e : Lam (σs ++ Γ) τ) → (ds : All (Lam Γ) σs) → (usnds : All2 USN ds) → USN (bindp e ds)
  lem σs (var x) ds usnds = {!!}
  usn (lem σs (app {σ = σ} e₁ e₂) ds usnds) τs args es usnes = usn (lem σs e₁ ds usnds) (σ , τs) args (bindp e₂ ds , es) (lem σs e₂ ds usnds , usnes) 
    -- e₁ : Lam (σs ++ Γ) (σ ⇒ τ)
    -- e₂ : Lam (σs ++ Γ) σ
  usn (lem {Γ} {τ} σs (lam {σ = σ} e) ds usnds) ε args ε ε = {!usn (lem σs e* _ _) ε _ ε ε!}
    where
      e* : Lam (σs ++ (σ , Γ)) τ
      e* = {!!}

      lem1 : USN (bindp e* (mapAll (mapLam there) ds))
      lem1 = lem σs e* (mapAll (mapLam there) ds) {!!}

      snLam : ∀ {Γ σ τ} → (e : Lam (σ , Γ) τ) → SN e → SN (lam e)
      snLam = {!!}
  usn (lem σs (lam {σ = σ} e) ds usnds) (τ₁ , τs) r (e₁ , es) usnes = {!!}
    -- e : Lam (σ , (σs ++ Γ)) τ
    where
      lem1 : {!!}
      lem1 = {!lem (σ , σs) e!}
