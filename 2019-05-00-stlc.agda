{-# OPTIONS --type-in-type #-}
module Stlc where

data ⊥ : Set where

data Bool : Set where
  false true : Bool

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

mapMaybe : {A B : Set} → (A → B) → (Maybe A → Maybe B)
mapMaybe f nothing = nothing
mapMaybe f (just a) = just (f a)

record _×_ (A B : Set) : Set where
  constructor _,,_
  field
    fst : A 
    snd : B

infixr 0 _,_
data List (A : Set) : Set where
  ε : List A
  _,_ : A → List A → List A

mapList : {A B : Set} → (A → B) → (List A → List B)
mapList f ε = ε
mapList f (a , as) = f a , mapList f as

data _∈_ {A : Set} : A → List A → Set where
  here : ∀ {a as} → a ∈ (a , as)
  there : ∀ {a a' as} → a ∈ as → a ∈ (a' , as)

data All {A : Set} : List A → (A → Set) → Set where
  ε : ∀ {P} → All ε P
  _,_ : ∀ {P a as} → P a → All as P → All (a , as) P

all : ∀ {A} {as : List A} {P : A → Set} → All as P → (∀ {a} → a ∈ as → P a)
all (p , ps) here = p
all (p , ps) (there i) = all ps i

data Eq {A : Set} (a : A) : A → Set where
  refl : Eq a a

data Sort : Set where
  ⋆ : Sort
  ⊥ˢ ⊤ˢ : Sort
  _+ˢ_ _×ˢ_ : Sort → Sort → Sort
  _⇒ˢ_ : Sort → Sort → Sort
  ⋆⇒ˢ : Sort → Sort
  ⋆⇒ˢ⋆ : Sort
  listˢ : Sort → Sort

data Type : (Δ : Set) → Set where
  var : ∀ {Δ} → Δ → Type Δ
  σ π : ∀ {Δ} → List (Type Δ) → Type Δ
  μ ν : ∀ {Δ} → Type (Maybe Δ) → Type Δ

infixr 5 _⊨_
data _⊨_ : Sort → Sort → Set where
  id : ∀ {s} → s ⊨ s
  _∘ˢ_ : ∀ {s t u} → t ⊨ u → s ⊨ t → s ⊨ u

  ⊥ˢ-elim : ∀ {u} → ⊥ˢ ⊨ u

  ⊤ˢ-intr : ∀ {u} → u ⊨ ⊤ˢ

  +ˢ-intr₁ : ∀ {s₁ s₂} → s₁ ⊨ s₁ +ˢ s₂
  +ˢ-intr₂ : ∀ {s₁ s₂} → s₂ ⊨ s₁ +ˢ s₂
  +ˢ-elim : ∀ {u s₁ s₂} → s₁ ⊨ u → s₂ ⊨ u → s₁ +ˢ s₂ ⊨ u

  ×ˢ-intr : ∀ {u s₁ s₂} → u ⊨ s₁ → u ⊨ s₂ → u ⊨ s₁ ×ˢ s₂
  ×ˢ-elim₁ : ∀ {s₁ s₂} → s₁ ×ˢ s₂ ⊨ s₁
  ×ˢ-elim₂ : ∀ {s₁ s₂} → s₁ ×ˢ s₂ ⊨ s₂

  ⇒ˢ-intr : ∀ {u s₁ s₂} → u ×ˢ s₁ ⊨ s₂ → u ⊨ s₁ ⇒ˢ s₂
  ⇒ˢ-elim : ∀ {u s₁ s₂} → u ⊨ s₁ ⇒ˢ s₂ → u ×ˢ s₁ ⊨ s₂

  ⋆⇒ˢ-intr : ∀ {u s} → u ×ˢ ⋆ ⊨ s → u ⊨ ⋆⇒ˢ s
  ⋆⇒ˢ-elim : ∀ {u s} → u ⊨ ⋆⇒ˢ s → u ×ˢ ⋆ ⊨ s

  ⋆⇒ˢ⋆-intr : ∀ {u} → u ×ˢ ⋆ ⊨ ⋆ → u ⊨ ⋆⇒ˢ⋆
  ⋆⇒ˢ⋆-elim : ∀ {u} → u ⊨ ⋆⇒ˢ⋆ → u ×ˢ ⋆ ⊨ ⋆

  list-intr₁ : ∀ {s} → ⊤ˢ ⊨ listˢ s
  list-intr₂ : ∀ {s} → s ×ˢ listˢ s ⊨ listˢ s
  list-elim : ∀ {u s} → ⊤ˢ ⊨ u → s ×ˢ u ⊨ u → listˢ s ⊨ u

  σ π : listˢ ⋆ ⊨ ⋆
  μ ν : (⋆ ⇒ˢ ⋆) ⊨ ⋆

appˢ : ∀ {u s₁ s₂} → u ⊨ s₁ ⇒ˢ s₂ → u ⊨ s₁ → u ⊨ s₂
appˢ f x = ⇒ˢ-elim f ∘ˢ ×ˢ-intr id x

infixr 5 _⊢'_
{-# NO_POSITIVITY_CHECK #-}
data _⊢'_ : {s t : Sort} → (σ τ : s ⊨ t) → Set where
  id : ∀ {s t} {τ : s ⊨ t} → τ ⊢' τ
  _∘'_ : ∀ {s t} {ρ σ τ : s ⊨ t} → σ ⊢' τ → ρ ⊢' σ → ρ ⊢' τ

  σ-intr : ∀ {u} {τ : u ⊨ ⋆} {τs : u ⊨ listˢ ⋆} → {!!} → τ ⊢' (σ ∘ˢ τs)
  --σ-elim : ∀ {ρ τs} → (∀ {τ} → τ ∈ τs → τ ⊢' ρ) → σ τs ⊢' ρ

  --π-intr : ∀ {ρ τs} → (∀ {τ} → τ ∈ τs → ρ ⊢' τ) → ρ ⊢' π τs
  --π-elim : ∀ {τs τ} → τ ∈ τs → π τs ⊢' τ

  --μ-intr : ∀ {τ} → τ # μ τ ⊢' μ τ
  --μ-elim : ∀ {ρ τ} → τ # ρ ⊢' ρ → μ τ ⊢' ρ

  --ν-intr : ∀ {ρ τ} → ρ ⊢' τ # ρ → ρ ⊢' ν τ
  --ν-elim : ∀ {τ} → ν τ ⊢' τ # ν τ

{-# TERMINATING #-}
mapType : ∀ {A B} → (A → B) → (Type A → Type B)
mapType f (var a) = var (f a)
mapType f (σ τs) = σ (mapList (mapType f) τs)
mapType f (π τs) = π (mapList (mapType f) τs)
mapType f (μ τ) = μ (mapType (mapMaybe f) τ)
mapType f (ν τ) = ν (mapType (mapMaybe f) τ)

{-# TERMINATING #-}
bind : ∀ {A B} → (A → Type B) → (Type A → Type B)
bind f (var a) = f a
bind f (σ τs) = σ (mapList (bind f) τs)
bind f (π τs) = π (mapList (bind f) τs)
bind f (μ τ) = μ (bind (\{ nothing → var nothing ; (just a) → mapType just (f a) }) τ)
bind f (ν τ) = ν (bind (\{ nothing → var nothing ; (just a) → mapType just (f a) }) τ)

_#_ : ∀ {Δ} → Type (Maybe Δ) → Type Δ → Type Δ
τ # ρ = bind (\{ nothing → ρ ; (just x) → var x }) τ

! : ∀ {Δ} → Type Δ → Type (Maybe Δ)
! τ = mapType just τ

{-
  ! τ # ρ
= bind (foo ρ) (map just τ)
= bind (foo ρ)
-}

!! : ∀ {Δ} → Type ⊥ → Type Δ
!! τ = mapType (\()) τ

infixr 5 _⊢_
infixr 10 _∘_
{-# NO_POSITIVITY_CHECK #-}
data _⊢_ {Δ : Set} : (σ τ : Type Δ) → Set where
  id : ∀ {τ} → τ ⊢ τ
  _∘_ : ∀ {ρ σ τ} → σ ⊢ τ → ρ ⊢ σ → ρ ⊢ τ

  σ-intr : ∀ {τs τ} → τ ∈ τs → τ ⊢ σ τs
  σ-elim : ∀ {ρ τs} → (∀ {τ} → τ ∈ τs → τ ⊢ ρ) → σ τs ⊢ ρ

  π-intr : ∀ {ρ τs} → (∀ {τ} → τ ∈ τs → ρ ⊢ τ) → ρ ⊢ π τs
  π-elim : ∀ {τs τ} → τ ∈ τs → π τs ⊢ τ

  μ-intr : ∀ {τ} → τ # μ τ ⊢ μ τ
  μ-elim : ∀ {ρ τ} → τ # ρ ⊢ ρ → μ τ ⊢ ρ

  ν-intr : ∀ {ρ τ} → ρ ⊢ τ # ρ → ρ ⊢ ν τ
  ν-elim : ∀ {τ} → ν τ ⊢ τ # ν τ

infix 5 [_]_⊢_
data [_]_⊢_ {Δ : Set} : (Γ : Type Δ → Set) (σ τ : Type Δ) → Set where
  ctx : ∀ {Γ τ ρ} → Γ τ → [ Γ ] ρ ⊢ τ
  id : ∀ {Γ τ} → [ Γ ] τ ⊢ τ
  _▹'_ : ∀ {Γ Δ τ₁ τ₂ τ₃}
    → (∀ {ρ} → Δ ρ → [ Γ ] τ₁ ⊢ ρ) × ([ Γ ] τ₁ ⊢ τ₂)  -- [ Γ ] τ₁ ⊢ [ Δ ] τ₂
    → [ Δ ] τ₂ ⊢ τ₃
    → [ Γ ] τ₁ ⊢ τ₃

  {-
    id  : [Γ]τ ⊢ [Γ]τ
    _▹_ : [Γ]ρ ⊢ [Δ]σ, [Δ]σ ⊢ [Σ]τ → [Γ]ρ ⊢ [Σ]τ
  -}

  σ-intr : ∀ {Γ τs τ} → τ ∈ τs → [ Γ ] τ ⊢ σ τs
  σ-elim : ∀ {Γ ρ τs} → (∀ {τ} → τ ∈ τs → [ Γ ] τ ⊢ ρ) → [ Γ ] σ τs ⊢ ρ

  π-intr : ∀ {Γ ρ τs} → (∀ {τ} → τ ∈ τs → [ Γ ] ρ ⊢ τ) → [ Γ ] ρ ⊢ π τs
  π-elim : ∀ {Γ τs τ} → τ ∈ τs → [ Γ ] π τs ⊢ τ

  μ-intr : ∀ {Γ τ} → [ Γ ] τ # μ τ ⊢ μ τ
  μ-elim : ∀ {Γ ρ τ} → [ Γ ] τ # ρ ⊢ ρ → [ Γ ] μ τ ⊢ ρ

  ν-intr : ∀ {Γ ρ τ} → [ Γ ] ρ ⊢ τ # ρ → [ Γ ] ρ ⊢ ν τ
  ν-elim : ∀ {Γ τ} → [ Γ ] ν τ ⊢ τ # ν τ

module _ where
  ∅ : ∀ {A : Set} → A → Set
  ∅ _ = ⊥

  tPair : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  tPair τ₁ τ₂ = π (τ₁ , τ₂ , ε)

  ePair' : ∀ {Δ} {Γ : Type Δ → Set} {ρ τ₁ τ₂ : Type Δ} → [ Γ ] ρ ⊢ τ₁ → [ Γ ] ρ ⊢ τ₂ → [ Γ ] ρ ⊢ tPair τ₁ τ₂
  ePair' f g = π-intr (all (f , g , ε))

  eFst' : ∀ {Δ} {Γ : Type Δ → Set} {τ₁ τ₂ : Type Δ} → [ Γ ] tPair τ₁ τ₂ ⊢ τ₁
  eFst' = π-elim here

  eSnd' : ∀ {Δ} {Γ : Type Δ → Set} {τ₁ τ₂ : Type Δ} → [ Γ ] tPair τ₁ τ₂ ⊢ τ₂
  eSnd' = π-elim (there here)

  tEither : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  tEither τ₁ τ₂ = σ (τ₁ , τ₂ , ε)

  eLeft' : ∀ {Δ} {Γ : Type Δ → Set} {τ₁ τ₂ : Type Δ} → [ Γ ] τ₁ ⊢ tEither τ₁ τ₂
  eLeft' = σ-intr here

  eRight' : ∀ {Δ} {Γ : Type Δ → Set} {τ₁ τ₂ : Type Δ} → [ Γ ] τ₂ ⊢ tEither τ₁ τ₂
  eRight' = σ-intr (there here)

  infixr 15 _×ᵗ_
  _×ᵗ_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  _×ᵗ_ = tPair

  infixr 14 _+ᵗ_
  _+ᵗ_ : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  _+ᵗ_ = tEither

  -- [∅] τ₁ × (τ₂ + τ₃) ⊢ τ₁ × τ₂ + τ₁ × τ₃
  distributivity : ∀ {Δ} {τ₁ τ₂ τ₃ : Type Δ} → [ ∅ ] (τ₁ ×ᵗ (τ₂ +ᵗ τ₃)) ⊢ (τ₁ ×ᵗ τ₂ +ᵗ τ₁ ×ᵗ τ₃)
  distributivity = ((\{ refl → eFst' }) ,, eSnd') ▹' lem where
    -- [τ₁] τ₂ + τ₃ ⊢ τ₁ × τ₂ + τ₁ × τ₃
    lem : ∀ {Δ} {τ₁ τ₂ τ₃ : Type Δ} → [ Eq τ₁ ] (τ₂ +ᵗ τ₃) ⊢ (τ₁ ×ᵗ τ₂ +ᵗ τ₁ ×ᵗ τ₃)
    lem {_} {τ₁} {τ₂} {τ₃} =
      σ-elim (all {P = λ τ → [ Eq τ₁ ] τ ⊢ τ₁ ×ᵗ τ₂ +ᵗ τ₁ ×ᵗ τ₃}
        ( (((\{ refl → ctx refl }) ,, ePair' (ctx refl) id) ▹' eLeft' {Γ = Eq τ₁})
        , (((\{ refl → ctx refl }) ,, ePair' (ctx refl) id) ▹' eRight' {Γ = Eq τ₁})
        , ε
      ))

_#^'_ : ∀ {Δ} {Γ : Type Δ → Set} {ρ₁ ρ₂ : Type Δ} → (τ : Type (Maybe Δ)) → [ Γ ] ρ₁ ⊢ ρ₂ → [ Γ ] τ # ρ₁ ⊢ τ # ρ₂
_#^'_ = {!!}

infix 5 _⇒'_
data _⇒'_ {Δ} : {Γ : Type Δ → Set} → {σ τ : Type Δ} → (f g : [ Γ ] σ ⊢ τ) → Set where
{-
  left-unit : ∀ {σ τ} {f : [ Γ ] σ ⊢ τ}
    → id ∘ f ⇒' f
  right-unit : ∀ {σ τ} {f : σ ⊢ τ}
    → f ∘ id ⇒' f
  assoc : ∀ {τ₁ τ₂ τ₃ τ₄} {f : τ₃ ⊢ τ₄} {g : τ₂ ⊢ τ₃} {h : τ₁ ⊢ τ₂}
    → f ∘ (g ∘ h) ⇒' (f ∘ g) ∘ h
-}

{-
  σ-rule : ∀ {Γ τs τ ρ} {r : ∀ {τ} → τ ∈ τs → [ Γ ] τ ⊢ ρ} {i : τ ∈ τs}
    → σ-elim r ∘ σ-intr i ⇒' r i
  π-rule : ∀ {Γ τs τ ρ} {r : ∀ {τ} → τ ∈ τs → ρ ⊢ τ} {i : τ ∈ τs}
    → π-elim i ∘ π-intr r ⇒' r i

  μ-rule : ∀ {Γ τ ρ} {r : τ # ρ ⊢ ρ}
    → μ-elim {τ = τ} r ∘ μ-intr ⇒' r ∘ (τ #^' μ-elim {τ = τ} r)
  ν-rule : ∀ {Γ τ ρ} {r : ρ ⊢ τ # ρ}
    → ν-elim ∘ ν-intr {τ = τ} r ⇒' (τ #^' ν-intr {τ = τ} r) ∘ r
    -}

_▹_ : ∀ {Δ} {ρ σ τ : Type Δ} → ρ ⊢ σ → σ ⊢ τ → ρ ⊢ τ
f ▹ g = g ∘ f

_#^_ : ∀ {Δ} {ρ₁ ρ₂ : Type Δ} → (τ : Type (Maybe Δ)) → ρ₁ ⊢ ρ₂ → τ # ρ₁ ⊢ τ # ρ₂
_#^_ = {!!}

infix 5 _⇒_
data _⇒_ {Δ} : {σ τ : Type Δ} → (f g : σ ⊢ τ) → Set where
  left-unit : ∀ {σ τ} {f : σ ⊢ τ}
    → id ∘ f ⇒ f
  right-unit : ∀ {σ τ} {f : σ ⊢ τ}
    → f ∘ id ⇒ f
  assoc : ∀ {τ₁ τ₂ τ₃ τ₄} {f : τ₃ ⊢ τ₄} {g : τ₂ ⊢ τ₃} {h : τ₁ ⊢ τ₂}
    → f ∘ (g ∘ h) ⇒ (f ∘ g) ∘ h

  σ-rule : ∀ {τs τ ρ} {r : ∀ {τ} → τ ∈ τs → τ ⊢ ρ} {i : τ ∈ τs}
    → σ-elim r ∘ σ-intr i ⇒ r i
  π-rule : ∀ {τs τ ρ} {r : ∀ {τ} → τ ∈ τs → ρ ⊢ τ} {i : τ ∈ τs}
    → π-elim i ∘ π-intr r ⇒ r i

  μ-rule : ∀ {τ ρ} {r : τ # ρ ⊢ ρ}
    → μ-elim {τ = τ} r ∘ μ-intr ⇒ r ∘ (τ #^ μ-elim {τ = τ} r)
  ν-rule : ∀ {τ ρ} {r : ρ ⊢ τ # ρ}
    → ν-elim ∘ ν-intr {τ = τ} r ⇒ (τ #^ ν-intr {τ = τ} r) ∘ r

module Turing (tR : Type ⊥) where
  var0 : ∀ {Δ} → Type (Maybe Δ)
  var0 = var nothing

  t⊤ : Type ⊥
  t⊤ = π ε

  tBool : Type ⊥
  tBool = σ (t⊤ , t⊤ , ε)

  ePair : ∀ {Δ} {ρ τ₁ τ₂ : Type Δ} → ρ ⊢ τ₁ → ρ ⊢ τ₂ → ρ ⊢ tPair τ₁ τ₂
  ePair f g = π-intr (all (f , g , ε))

  eFst : ∀ {Δ} {τ₁ τ₂ : Type Δ} → tPair τ₁ τ₂ ⊢ τ₁
  eFst = π-elim here

  eSnd : ∀ {Δ} {τ₁ τ₂ : Type Δ} → tPair τ₁ τ₂ ⊢ τ₂
  eSnd = π-elim (there here)

  eLeft : ∀ {Δ} {τ₁ τ₂ : Type Δ} → τ₁ ⊢ tEither τ₁ τ₂
  eLeft = σ-intr here

  eRight : ∀ {Δ} {τ₁ τ₂ : Type Δ} → τ₂ ⊢ tEither τ₁ τ₂
  eRight = σ-intr (there here)

  eCaseEither : ∀ {Δ} {τ₁ τ₂ ρ : Type Δ} → τ₁ ⊢ ρ → τ₂ ⊢ ρ → tEither τ₁ τ₂ ⊢ ρ
  eCaseEither f g = σ-elim (all (f , g , ε))

  tMaybe : ∀ {Δ} → Type Δ → Type Δ
  tMaybe τ = σ (!!  t⊤ , τ , ε)

  tStream : ∀ {Δ} → Type Δ → Type Δ
  tStream τ = ν (tPair (! τ) var0)

  tState : Type ⊥
  tState = tPair (tStream tBool) (tStream tBool)

  eSWrite : Bool → tState ⊢ tState
  eSWrite = {!eFst!}

  {-
    writeT : Bool ⟶ ⊤
    read   : ⊤ ⟶ Bool
    left   : ⊤ ⟶ ⊤
    right  : ⊤ ⟶ ⊤
    exit   : tBool ⟶ ⊥
  -}
  tCode' : ∀ {Δ} → Type Δ → Type Δ
  tCode' ρ = σ
    ( tPair (!! tBool) ρ
    , tPair ρ ρ
    , ρ
    , ρ
    , !! tBool
    , ε
    )

  tCode : Type ⊥
  tCode = ν (tCode' var0)

  {-
    step ((ls , cur:rs)   , write b c') = right ((ls , b:rs) , c')
    step (s@(_ , false:_) , read c1 c2) = right (s , c1)
    step (s@(_ , true:_)  , read c1 c2) = right (s , c2)
    step ((ls , cur:rs)   , left c')    = right ((cur:ls , rs) , c')
    step ((l:ls , rs)     , right c')   = right ((ls , l:rs) ,  c')
    step (_               , exit r)     = left r
  -}
  step : tPair tState tCode ⊢ tEither tBool (tPair tState tCode)
  step = {!ν-elim ∘ eSnd!}
  {-
    ( {!!}
    , {!!}
    , {!!}
    , {!!}
    , eLeft
    , ε))
    -}

  tDelay : ∀ {Δ} → Type Δ → Type Δ
  tDelay τ = ν (tEither (! τ) var0) 

  loop : ∀ {Δ} {τ ρ : Type Δ} → ρ ⊢ tEither τ ρ → ρ ⊢ tDelay τ
  loop f = ν-intr {!f!}
   -- eCaseEither eNow ({!!} ∘ f) ∘ f

  run : tPair tState tCode ⊢ tDelay tBool
  run = loop step
