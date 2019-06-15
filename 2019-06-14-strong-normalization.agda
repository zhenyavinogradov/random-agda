module _ where

module _ where
  -- types
  module _ where
    data ⊥ : Set where
  
    data List (A : Set) : Set where
      ε : List A
      _∷_ : A → List A → List A

  -- function
  module _ where
    _∘_ : ∀ {A B C} → (B → C) → (A → B) → (A → C)
    (f ∘ g) a = f (g a)

    identity : ∀ {A} → A → A
    identity a = a

  -- list
  module _ where
    _++_ : ∀ {A} → List A → List A → List A
    ε ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
    
    data In {A : Set} : List A → A → Set where
      here : ∀ {a as} → In (a ∷ as) a
      there : ∀ {a a' as} → In as a → In (a' ∷ as) a

    data All {A : Set} (P : A → Set) : List A → Set where
      ε : All P ε
      _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

    data All2 {A : Set} {P : A → Set} (P2 : {a : A} → P a → Set) : {as : List A} (Pas : All P as) → Set where
      ε : All2 P2 ε
      _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} → P2 Pa → All2 P2 Pas → All2 P2 (Pa ∷ Pas)

    mapAll : {A : Set} {P Q : A → Set} → ({a : A} → P a → Q a) → {as : List A} → All P as → All Q as
    mapAll f ε = ε
    mapAll f (x ∷ Pas) = f x ∷ mapAll f Pas

    get : ∀ {A} {P : A → Set} {a as} → All P as → In as a → P a
    get (Pa ∷ Ps) here = Pa
    get (Pa ∷ Ps) (there i) = get Ps i

  -- pred
  module _ where
    Pred : Set → Set₁
    Pred A = A → Set

    _⊆_ : {A : Set} → Pred A → Pred A → Set
    P ⊆ Q = ∀ {a} → P a → Q a

    ⊆identity : {A : Set} → (P : Pred A) → P ⊆ P
    ⊆identity P Pa = Pa

    ⊆compose : {A : Set} → {P Q R : Pred A} → P ⊆ Q → Q ⊆ R → P ⊆ R
    ⊆compose P⊆Q Q⊆R Pa = Q⊆R (P⊆Q Pa)

    data _<+_ {A : Set} (a : A) (P : A → Set) : A → Set where
      here : (a <+ P) a
      there : ∀ {a'} → P a' → (a <+ P) a'

    _⊆<+_ : ∀ {A} → (a : A) → {P Q : A → Set} → P ⊆ Q → (a <+ P) ⊆ (a <+ Q)
    (a ⊆<+ F) here = here
    (a ⊆<+ F) (there i) = there (F i)

    data _<+>_ {A : Set} (P Q : A → Set) (a : A) : Set where
      inl : P a → (P <+> Q) a
      inr : Q a → (P <+> Q) a

  -- iso
  module _ where
    data _≡_ {A : Set} (a : A) : A → Set where
      refl : a ≡ a

    record Iso (A B : Set) : Set where
      field
        to : A → B
        from : B → A
        to∘from : ∀ {a} → to (from a) ≡ a
        from∘to : ∀ {a} → from (to a) ≡ a
    open Iso public

-- ##########
module _ (Θ : Set) where
  data Type : Set where
    atom : Θ → Type
    _⇒_ : Type → Type → Type

  Context : Set₁
  Context = Type → Set

  EqBag : Context → Context → Set
  EqBag Γ Δ = (τ : Type) → Iso (Γ τ) (Δ τ)

  data Lam : Context → Type → Set where
    var : ∀ {Γ τ} → Γ τ → Lam Γ τ
    app : ∀ {Γ σ τ} → Lam Γ (σ ⇒ τ) → Lam Γ σ → Lam Γ τ
    abs : ∀ {Γ σ τ} → Lam (σ <+ Γ) τ → Lam Γ (σ ⇒ τ)

  app≡ : ∀ {Γ σ τ} → {e₁ e₁' : Lam Γ (σ ⇒ τ)} → {e₂ e₂' : Lam Γ σ} → e₁ ≡ e₁' → e₂ ≡ e₂' → app e₁ e₂ ≡ app e₁' e₂'
  app≡ refl refl = refl

  mapLam : ∀ {Γ Δ τ} → Γ ⊆ Δ → Lam Γ τ → Lam Δ τ
  mapLam f (var x) = var (f x)
  mapLam f (app e e') = app (mapLam f e) (mapLam f e')
  mapLam f (abs e) = abs (mapLam (_ ⊆<+ f) e)

  mapLamIdentity : ∀ {Γ τ} → (e : Lam Γ τ) → mapLam (⊆identity Γ) e ≡ e
  mapLamIdentity (var x) = refl
  mapLamIdentity (app e e') = app≡ (mapLamIdentity e) (mapLamIdentity e')
  mapLamIdentity (abs e) = {!mapLamIdentity e!}

  EqLam : ∀ {Γ Γ'} → EqBag Γ Γ' → ∀ {τ} → Lam Γ τ → Lam Γ' τ → Set
  EqLam = {!!}

  IsoLam : ∀ {Γ Δ τ} → EqBag Γ Δ → Iso (Lam Γ τ) (Lam Δ τ)
  to (IsoLam eqBag) e = mapLam (\{τ : Type} → \Γτ → to (eqBag τ) Γτ) e
  from (IsoLam eqBag) e = mapLam (\{τ : Type} → \Γτ → from (eqBag τ) Γτ) e
  to∘from (IsoLam eqBag) = {!!}
  from∘to (IsoLam eqBag) = {!!}

  binds : ∀ {Γ Δ τ} → Lam Γ τ → (Γ ⊆ Lam Δ) → Lam Δ τ
  binds (var x) ds = ds x
  binds (app e e') ds = app (binds e ds) (binds e' ds)
  binds (abs e) ds = abs (binds e \{ here → var here ; (there x) → mapLam there (ds x) })

  bindsa : ∀ {Γ Γ' τ} → Lam (Γ' <+> Γ) τ → (Γ' ⊆ Lam Γ) → Lam Γ τ
  bindsa e ds = binds e \{ (inl x) → ds x ; (inr y) → var y  }

  data Red {Γ τ} : Lam Γ τ → Lam Γ τ → Set where

  record InfRed {A : Set} (R : A → A → Set) (head : A) : Set where
    coinductive
    field
      next : A
      step : R head next
      tail : InfRed R next

  SN : ∀ {Γ τ} → Lam Γ τ → Set
  SN e = InfRed Red e → ⊥

  _*⇒_ : List Type → Type → Type
  ε *⇒ τ = τ
  (σ ∷ σs) *⇒ τ = σ ⇒ (σs *⇒ τ)

  app* : ∀ {Γ σs τ} → Lam Γ (σs *⇒ τ) → All (Lam Γ) σs → Lam Γ τ
  app* e ε = e
  app* e (e' ∷ es) = app* (app e e') es
  
  data Args (σs : List Type) (τ : Type) : Type → Set where
    args : Args σs τ (σs *⇒ τ)

  fromArgs : ∀ {ts σs τ τ'} → Args σs τ τ' → Lam ts (σs *⇒ τ) → Lam ts τ'
  fromArgs args e = e

  toArgs : ∀ {ts σs τ τ'} → Args σs τ τ' → Lam ts τ' → Lam ts (σs *⇒ τ)
  toArgs args e = e

  {-# NO_POSITIVITY_CHECK #-}
  record USN {Γ τ'} (e : Lam Γ τ') : Set where
    field usn : (σs : List Type) → (τ : Type) → (r : Args σs τ τ') → (es : All (Lam Γ) σs) → (usnes : All2 USN es) → SN (app* (toArgs r e) es)
  open USN public

  All2P : {A : Set} (P : A → Set) {Q : A → Set} → (Q2 : {a : A} → Q a → Set) → (F : {a : A} → P a → Q a) → Set
  All2P {A} P Q2 F = {a : A} → (Pa : P a) → Q2 (F Pa)

  postulate
    tr : {Γ Γ' : Context} → (eqBag : EqBag Γ Γ') → ∀ {τ} → (e : Lam Γ τ) (e' : Lam Γ' τ) → (P : ∀ {Γ#} → Lam Γ# τ → Set) → P e → P {!mapLam (to (eqBag τ))!}

  lem : ∀ Γ σs τ → (e : Lam (σs <+> Γ) τ) → (ds : σs ⊆ Lam Γ) → (usnds : All2P σs USN ds) → USN (bindsa e ds)
  lem Γ σs τ (var (inl x)) ds usnds = usnds x
  usn (lem Γ σs .(τs *⇒ τ) (var (inr x)) ds usnds) τs τ args es usnes = {!!}
  usn (lem Γ σs .(τs *⇒ τ) (app {σ = σ} e₁ e₂) ds usnds) τs τ args es usnes = usn (lem Γ σs _ e₁ ds usnds) (σ ∷ τs) τ args (bindsa e₂ ds ∷ es) (lem Γ σs _ e₂ ds usnds ∷ usnes)
  usn (lem Γ σs .(σ ⇒ τ) (abs {σ = σ} {τ = τ} e) ds usnds) .ε .(σ ⇒ τ) args ε ε = {!lem Γ (σ <+ σs) _ !}
  usn (lem Γ σs .(σ ⇒ (τs *⇒ τ)) (abs {σ = σ} e) ds usnds) (σ ∷ τs) τ args (e₁ ∷ es) (usne₁ ∷ usnes) = {!lem Γ!}
