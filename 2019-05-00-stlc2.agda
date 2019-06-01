{-# OPTIONS --type-in-type #-}
module Stlc2 where

-- generic
module _ where
  -- function
  module _ where
    compose : {A B C : Set} → (A → B) → (B → C) → (A → C)
    compose f g a = g (f a)

  -- equaity
  module _ where
    data Eq {A : Set} (a : A) : A → Set where
      refl : Eq a a

  -- finite (co)products
  module _ where
    data ⊥ : Set where

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

  -- predicate
  module _  where
    ∅ : {A : Set} → A → Set
    ∅ _ = ⊥

  -- natural
  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

  -- fin
  module _ where
    data Fin : ℕ → Set where
      zero : ∀ {n} → Fin (succ n)
      succ : ∀ {n} → Fin n → Fin (succ n)

    finAppend : ∀ {n} {A : Set} → (Fin n → A) → A → (Fin (succ n) → A)
    finAppend f a zero = a
    finAppend f a (succ i) = f i

  -- maybe
  module _ where
    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just : A → Maybe A

    mapMaybe : ∀ {A B} → (A → B) → (Maybe A → Maybe B)
    mapMaybe f nothing = nothing
    mapMaybe f (just a) = just (f a)
  
  -- list
  module _ where
    infixr 5 _,_
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

    single : {A : Set} → A → List A
    single a = a , ε

    mapList : ∀ {A B} → (A → B) → (List A → List B)
    mapList f ε = ε
    mapList f (a , as) = f a , mapList f as

    forEachList : ∀ {A B} → List A → (A → B) → List B
    forEachList as f = mapList f as

    data _∈_ {A : Set} : A → List A → Set where
      here : ∀ {a as} → a ∈ (a , as)
      there : ∀ {a a' as} → a ∈ as → a ∈ (a' , as)

    module _ {A : Set} {a : A} {as : List A} where
      lFirst : a ∈ (a , as)
      lFirst = here

      lSecond : ∀ {a'} → a ∈ (a' , a , as)
      lSecond = there here

      lThird : ∀ {a' a''} → a ∈ (a' , a'' , a , as)
      lThird = there (there here)

    data All {A : Set} : List A → (P : A → Set) → Set where
      ε : ∀ {P} → All ε P
      _,_ : ∀ {a as P} → P a → All as P → All (a , as) P

    all : {A : Set} {as : List A} {P : A → Set} → All as P → {a : A} → a ∈ as → P a
    all (p , ps) here = p
    all (p , ps) (there i) = all ps i

    each : {A : Set} {P : A → Set} → (as : List A) → ({a : A} → a ∈ as → P a) → All as P
    each ε f = ε
    each (a , as) f = f here , each as (compose there f)

TCtx : Set
TCtx = ℕ

infix 25 !_
data Type : (Δ : TCtx) → Set where
  var : ∀ {Δ} → Fin Δ → Type Δ
  !_  : ∀ {Δ} → Type Δ → Type (succ Δ)
  σ π : ∀ {Δ} → List (Type Δ) → Type Δ
  μ ν : ∀ {Δ} → Type (succ Δ) → Type Δ

{-# TERMINATING #-}
bindType : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → Type Δ₂) → (Type Δ₁ → Type Δ₂)
bindType f (var x) = f x
bindType f (! τ) = bindType (compose succ f) τ
bindType f (σ τs) = σ (mapList (bindType f) τs)
bindType f (π τs) = π (mapList (bindType f) τs)
bindType f (μ τ) = μ (bindType (finAppend (compose f !_) (var zero)) τ)
bindType f (ν τ) = ν (bindType (finAppend (compose f !_) (var zero)) τ)

mapType : ∀ {Δ₁ Δ₂} → (Fin Δ₁ → Fin Δ₂) → (Type Δ₁ → Type Δ₂)
mapType f τ = bindType (compose f var) τ

subst : ∀ {Δ} → Type (succ Δ) → Fin (succ Δ) → Type Δ → Type Δ
subst (var zero) zero ρ = ρ
subst (var (succ j)) (succ i) ρ = {!!}
subst (var j) i ρ = {!var j!}
subst (! τ) i ρ = {!!}
subst (σ x) i ρ = {!!}
subst (π x) i ρ = {!!}
subst (μ τ) i ρ = {!!}
subst (ν τ) i ρ = ν (subst τ (succ i) {!ρ!})

_#_ : ∀ {Δ} → Type (succ Δ) → Type Δ → Type Δ
τ # ρ = bindType (\{ zero → ρ ; (succ i) → var i }) τ

Ctx : TCtx → Set
Ctx Δ = List (Type Δ)

infix 5 [_]_⊢_
infixr 10 _∘_
{-# NO_POSITIVITY_CHECK #-}
data [_]_⊢_ {Δ : TCtx} : Ctx Δ → Type Δ → Type Δ → Set where
  id : ∀ {Γ τ} → [ Γ ] τ ⊢ τ
  _∘_ : ∀ {Γ τ₁ τ₂ τ₃} → [ Γ ] τ₂ ⊢ τ₃ → [ Γ ] τ₁ ⊢ τ₂ → [ Γ ] τ₁ ⊢ τ₃

  idC : ∀ {Γ ρ τ} → τ ∈ Γ → [ Γ ] ρ ⊢ τ
  _∘C_ : ∀ {Γ₁ Γ₂ ρ τ} → [ Γ₂ ] ρ ⊢ τ → (All Γ₂ (\α → [ Γ₁ ] ρ ⊢ α)) → [ Γ₁ ] ρ ⊢ τ

  σ-intr : ∀ {Γ τ τs} → τ ∈ τs → [ Γ ] τ ⊢ σ τs
  σ-elim : ∀ {Γ ρ τs} → (All τs (\τ → [ Γ ] τ ⊢ ρ)) → [ Γ ] σ τs ⊢ ρ

  π-intr : ∀ {Γ ρ τs} → (All τs (\τ → [ Γ ] ρ ⊢ τ)) → [ Γ ] ρ ⊢ π τs
  π-elim : ∀ {Γ τ τs} → τ ∈ τs → [ Γ ] π τs ⊢ τ

  μ-intr : ∀ {Γ τ} → [ Γ ] τ # μ τ ⊢ μ τ
  μ-elim : ∀ {Γ τ ρ} → [ Γ ] τ # ρ ⊢ ρ → [ Γ ] μ τ ⊢ ρ

  ν-intr : ∀ {Γ τ ρ} → [ Γ ] ρ ⊢ τ # ρ → [ Γ ] ρ ⊢ ν τ
  ν-elim : ∀ {Γ τ} → [ Γ ] ν τ ⊢ τ # ν τ

  -- !-intr : ∀ {Γ τ ρ} → [ Γ ] (mapType succ τ) ⊢ ! τ

module _ {Δ : TCtx} {Γ : Ctx Δ} {ρ₁ ρ₂ : Type Δ} where
  {-# TERMINATING #-}
  _#^_ : (τ : Type (succ Δ)) → [ Γ ] ρ₁ ⊢ ρ₂ → [ Γ ] τ # ρ₁ ⊢ τ # ρ₂
  var zero #^ f = f
  var (succ i) #^ f = id
  ! τ #^ f = id
  σ τs #^ f = lem (each τs \{a = τ} _ → τ #^ f) where
    lem : All τs (\τ → [ Γ ] τ # ρ₁ ⊢ τ # ρ₂) → [ Γ ] σ τs # ρ₁ ⊢ σ τs # ρ₂
    lem r = σ-elim (each _ \i → σ-intr {!all r!})
  π τs #^ f = {!!}
  μ τ #^ f = {!!}
  ν τ #^ f = {!!}


-- for convieoence
module _ where
  tvar0 : ∀ {Δ} → Type (succ Δ)
  tvar0 = var zero


-- generic definitions
module _ where
  ν-wrap : ∀ {Δ} {Γ : Ctx Δ} {τ : Type (succ Δ)} → [ Γ ] τ # ν τ ⊢ ν τ
  ν-wrap {τ = τ} = ν-intr (τ #^ ν-elim)

  μ-unwrap : ∀ {Δ} {Γ : Ctx Δ} {τ : Type (succ Δ)} → [ Γ ] μ τ ⊢ τ # μ τ
  μ-unwrap {τ = τ} = μ-elim (τ #^ μ-intr)

  σ-elimOf
    : ∀ {Δ} {Γ : Ctx Δ} {τs : List (Type Δ)} {δ ρ}
    → [ Γ ] δ ⊢ σ τs → (All τs (\τ → [ δ , Γ ] τ ⊢ ρ)) → [ Γ ] δ ⊢ ρ
  σ-elimOf = {!!}

  μ-elimOf
    : ∀ {Δ} {Γ : Ctx Δ} {τ : Type (succ Δ)} {δ ρ}
    → [ Γ ] δ ⊢ μ τ → [ δ , Γ ] τ # ρ ⊢ ρ → [ Γ ] δ ⊢ ρ
  μ-elimOf = {!!}

  -- bottom and top
  module _ where
    t⊥ : Type zero
    t⊥ = σ ε 

    t⊤ : Type zero
    t⊤ = π ε 

  -- either
  module _ {Δ : TCtx} where
    tEither : Type Δ → Type Δ → Type Δ
    tEither τ₁ τ₂ = σ (τ₁ , τ₂ , ε)

    eEitherCase : ∀ {Γ ρ τ₁ τ₂} → [ Γ ] τ₁ ⊢ ρ → [ Γ ] τ₂ ⊢ ρ → [ Γ ] tEither τ₁ τ₂ ⊢ ρ
    eEitherCase f g = σ-elim (f , g , ε)

    eEitherLeft : ∀ {Γ τ₁ τ₂} → [ Γ ] τ₁ ⊢ tEither τ₁ τ₂
    eEitherLeft = σ-intr here

    eEitherRight : ∀ {Γ τ₁ τ₂} → [ Γ ] τ₂ ⊢ tEither τ₁ τ₂
    eEitherRight = σ-intr (there here)

  -- pair
  module _ {Δ : TCtx} where
    tPair : Type Δ → Type Δ → Type Δ
    tPair τ₁ τ₂ = π (τ₁ , τ₂ , ε)

    ePair : ∀ {Γ ρ τ₁ τ₂} → [ Γ ] ρ ⊢ τ₁ → [ Γ ] ρ ⊢ τ₂ → [ Γ ] ρ ⊢ tPair τ₁ τ₂
    ePair f g = π-intr (f , g , ε)

    ePairFst : ∀ {Γ τ₁ τ₂} → [ Γ ] tPair τ₁ τ₂ ⊢ τ₁
    ePairFst = π-elim here

    ePairSnd : ∀ {Γ τ₁ τ₂} → [ Γ ] tPair τ₁ τ₂ ⊢ τ₂
    ePairSnd = π-elim (there here)

  -- bool
  module _ where
    tBool : Type zero
    tBool = tEither t⊤ t⊤

    eFalse : ∀ {Γ} → [ Γ ] t⊤ ⊢ tBool
    eFalse = σ-intr here

    eTrue : ∀ {Γ} → [ Γ ] t⊤ ⊢ tBool
    eTrue = σ-intr (there here)

  tDelay : ∀ {Δ} → Type Δ → Type Δ
  tDelay τ = ν (tEither (! τ) tvar0)

  module _ {Δ : TCtx} where
    tStream : Type Δ → Type Δ
    tStream τ = ν (tPair (! τ) tvar0)

    eStreamHead : ∀ {Γ τ} → [ Γ ] tStream τ ⊢ τ
    eStreamHead = {!!} ∘ ν-elim

    eStreamTail : ∀ {Γ τ} → [ Γ ] tStream τ ⊢ tStream τ
    eStreamTail = ePairSnd ∘ ν-elim

-- turing machine
module _ where
  -- tape
  module _ where
    tTape : Type zero
    tTape = tPair (tStream tBool) (tStream tBool)

    eTapeLeft : ∀ {Γ} → [ Γ ] tTape ⊢ tTape
    eTapeLeft =
      ePair
      (ν-wrap ∘ ePair (eStreamHead ∘ ePairSnd) ePairFst)
      (eStreamTail ∘ ePairSnd)

    eTapeRight : ∀ {Γ} → [ Γ ] tTape ⊢ tTape
    eTapeRight =
      ePair
      (eStreamTail ∘ ePairFst)
      (ν-wrap ∘ ePair (eStreamHead ∘ ePairFst) ePairSnd)

    eTapeRead : ∀ {Γ} → [ Γ ] tTape ⊢ tBool
    eTapeRead = ePairFst ∘ ν-elim ∘ ePairFst

    eTapeWrite : ∀ {Γ} → [ Γ ] tPair tBool tTape ⊢ tTape
    eTapeWrite =
      ePair
      (ν-wrap ∘ ePair ePairFst (eStreamTail ∘ ePairFst ∘ ePairSnd))
      (ePairSnd ∘ ePairSnd)

  tR : Type zero
  tR = tBool

  tCode : Type zero
  tCode =
    ν (σ
      ( tPair tvar0 tvar0  -- read
      , tvar0              -- write false
      , tvar0              -- write true
      , tvar0              -- left
      , tvar0              -- right
      , ! tR               -- exit
      , ε
    ))

  eStep' : ∀ {ρ} → [ tTape , tCode , ε ] ρ ⊢ tEither tR (tPair tTape tCode)
  eStep' = σ-elimOf (ν-elim ∘ idC lSecond)
    ( eEitherRight ∘ ePair (idC lSecond) (σ-elimOf (eTapeRead ∘ idC lSecond) (ePairFst ∘ idC lFirst , ePairSnd ∘ idC lFirst , ε))
    , eEitherRight ∘ ePair (eTapeWrite ∘ ePair (eFalse ∘ π-intr ε) (idC lSecond) ) id
    , eEitherRight ∘ ePair (eTapeWrite ∘ ePair (eTrue ∘ π-intr ε) (idC lSecond) ) id
    , eEitherRight ∘ ePair (eTapeLeft ∘ idC lSecond) id
    , eEitherRight ∘ ePair (eTapeRight ∘ idC lSecond) id
    , eEitherLeft ∘ id
    , ε
    )

  eStep : [ ε ] tPair tTape tCode ⊢ tEither tR (tPair tTape tCode)
  eStep = eStep' ∘C (ePairFst , ePairSnd , ε)

  eRun : [ ε ] tPair tTape tCode ⊢ tDelay tR
  eRun = ν-intr eStep


module _ where
  data _⇒_ {Δ : TCtx} {Γ : Ctx Δ} {ρ τ : Type Δ} : (f g : [ Γ ] ρ ⊢ τ → [ Γ ] ρ ⊢ τ) → Set where

