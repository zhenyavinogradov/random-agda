{-# OPTIONS --type-in-type #-}
module _ where

module _ where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,,_
    field
      first : A
      second : B first
  open Σ public

  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data In {A : Set} : List A → A → Set where
    here : ∀ {a as} → In (a ∷ as) a
    there : ∀ {a a' as} → In as a → In (a' ∷ as) a

  at : {!!}
  at = {!!}

  Elem : {A : Set} → List A → Set
  Elem {A} as = Σ A \a → In as a

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  get : ∀ {A : Set} {P : A → Set} {τs τ} → All P τs → In τs τ → P τ
  get (Pa ∷ Pas) here = Pa
  get (Pa ∷ Pas) (there i) = get Pas i

  data All2 {A : Set} {P : A → Set} (P2 : (a : A) → P a → Set) : {as : List A} → All P as → Set where
    ε : All2 P2 ε
    _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} → P2 a Pa → All2 P2 Pas → All2 P2 (Pa ∷ Pas)

  postulate String : Set
  {-# BUILTIN STRING String #-}

module _ where
  record Var : Set where
    field
      v : String

  Vars : Set
  Vars = List Var

  Abs : Set → Set
  Abs X = Var × X

  data Type : Set where
    tvar  : ∀ {vs} → Elem vs → Type
    σ π  : List Type → Type
    μ ν  : Abs Type → Type
    _⇒_ : Type → Type → Type

{-
  {-# TERMINATING #-}
  lift : ∀ {v vs} → (i : In vs v) → Type (remove vs i) → Type vs
  lift i (var (x ,, j)) = var (x ,, wasThere i j)
  lift i (σ τs) = σ (mapList (lift i) τs)
  lift i (π τs) = π (mapList (lift i) τs)
  lift i (μ (x ,, ϕ)) = μ (x ,, lift (there i) ϕ)
  lift i (ν (x ,, ϕ)) = ν (x ,, lift (there i) ϕ)

  {-# TERMINATING #-}
  subst : ∀ {vs} → Type vs → (v : Var) → (i : In vs v) → Type (remove vs i) → Type (remove vs i)
  subst (var (x ,, i)) v j τ = var {!!} --bool (σ ?) τ (var {!!} )(eqIn i j)
  subst (σ τs) v i τ = σ (mapList (\α → subst α _ i τ) τs)
  subst (π τs) v i τ = π (mapList (\α → subst α _ i τ) τs)
  subst (μ (x ,, ϕ)) v i τ = μ (x ,, subst ϕ v (there i) (lift here τ))
  subst (ν (x ,, ϕ)) v i τ = ν (x ,, subst ϕ v (there i) (lift here τ))
  -}

  AbsType : Set
  AbsType = Abs Type

  _#_ : AbsType → Type → Type
  _#_ = {!!}
  -- (v ,, ϕ) # τ = subst ϕ v here τ

  Ctx : Set
  Ctx = List (Var × Type)

  data Term : Set where
    var : (v : Var) → Term

    σ-intr : (τs : List Type) → Elem τs → Term {- τᵢ -}→ Term
    σ-elim : List (Abs Term {- τᵢ → ρ -}) → Term {- σ τs -} → Term {- ρ -}

    π-intr : (τs : List Type) → List (Term {- τᵢ -}) → Term {- π τs -}
    π-elim : (τs : List Type) → Elem τs → Term {- π τs -} → Term {- τᵢ -}

    ⇒-intr : (ρ τ : Type) → Term {- ρ → τ -} → Term {- ρ ⇒ τ -}
    ⇒-elim : (ρ τ : Type) → Term {- ρ ⇒ τ -} → Term {- ρ -} → Term {- τ -}

    μ-intr : (ϕ : AbsType) → Term {- ϕ # μ ϕ -} → Term {- μ ϕ -}
    μ-elim : (ϕ : AbsType) → (ρ : Type) → Abs Term {- ϕ # ρ → ρ -} → Term {- μ ϕ -} → Term {- ρ -}

    ν-intr : (ϕ : AbsType) → (ρ : Type) → Abs Term {- ρ → ϕ # ρ -} → Term {- ρ -} → Term {- ν ϕ -}
    ν-elim : (ϕ : AbsType) → Term {- ν ϕ -} → Term {- ϕ # ν ϕ -}

  AbsTerm : Set
  AbsTerm = Abs Term

  map : (ϕ : AbsType) → (σ τ : Type) → (Term {- σ -} → Term {- τ -}) → (Term {- ϕ # σ -} → Term {- ϕ # τ -})
  map = {!!}

  _$_ : (ρ τ : Type) → AbsTerm {- ρ → τ -} → Term {- ρ -} → Term {- τ -}
  _$_ = {!!}

{-
  infix 5 _⇛_
  data _⇛_ : {τ : Type} → Term {- τ -} → Term {- τ -} → Set where
    σ-rule : ∀ (τs : List Type) (τ ρ : Type) (As : List (AbsTerm {- τᵢ → ρ -})) {i : In τs τ} → {t : Term {- τ -}} → σ-elim As (σ-intr ρ τ i t) ⇛ at As i $ t
    π-rule : ∀ {τ τs} {As : All (\α → Term {- α -}) τs} {i : In τs τ} → π-elim i (π-intr As) ⇛ get As i
    μ-rule : {ϕ : AbsType} {ρ : Type} {f : AbsTerm {- ϕ # ρ → ρ -}} → {t : Term {- ϕ # μ ϕ -}} → μ-elim ϕ f (μ-intr t) ⇛ (f $ map ϕ (μ-elim ϕ f) t)
    ν-rule : {ϕ : AbsType} {ρ : Type} {f : AbsTerm {- ρ → ϕ # ρ -}} → {t : Term {- ρ -}} → ν-elim (ν-intr ϕ f t) ⇛ map ϕ (ν-intr ϕ f) (f $ t)
    ⇒-rule : {ρ : Type} {τ : Type} {f : AbsTerm {- ρ → τ -}} → {t : Term {- ρ -}} → ⇒-elim ρ (⇒-intr ρ f) t ⇛ f $ t
    -}

  {-# TERMINATING #-}
  Usn : Type → Set
  Usn (tvar x) = Term
  Usn (σ τs) = Term × ((ρ : Type) → List (AbsTerm {- τᵢ → ρ -}) → Usn ρ)
  Usn (π τs) = Term × ((τ : Type) → In τs τ → Usn τ)
  Usn (ρ ⇒ τ) = Term × (Usn ρ → Usn τ)
  Usn (μ ϕ) = Term × ((ρ : Type) → Usn {- ϕ # ρ -} ρ → Usn ρ)
  Usn (ν ϕ) = Term × (Usn (ϕ # ν ϕ))

  -- σ-elim : ∀ {Γ τs ρ} → All (\τ → AbsT Term Γ τ ρ) τs → Term Γ (σ τs) → Term Γ ρ
  -- π-elim : ∀ {Γ τs τ} → In τs τ → Term Γ (π τs) → Term Γ τ
  -- ⇒-elim : ∀ {Γ τ} ρ → Term Γ (ρ ⇒ τ) → Term Γ (! ρ) → Term Γ τ
  -- μ-elim : ∀ {Γ ρ} ϕ → AbsT Term Γ (ϕ # ρ) ρ → Term Γ (μ ϕ) → Term Γ ρ
  -- ν-elim : ∀ {Γ ϕ} → Term Γ (ν ϕ) → Term Γ (ϕ # ν ϕ)
