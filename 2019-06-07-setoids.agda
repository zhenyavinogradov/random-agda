-- setoids
{-# OPTIONS --type-in-type #-}
module _ where

-- lib
module _ where
  -- types
  module _ where
    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just : A → Maybe A

    record _×_ (A B : Set) : Set where
      constructor _&_
      field
        fst : A
        snd : B
    open _×_ public

  module _ where
    mapMaybe : ∀ {A B} → (A → B) → (Maybe A → Maybe B)
    mapMaybe f nothing = nothing
    mapMaybe f (just x) = just (f x)

  -- pred
  module _ where
    data _+>_ {A : Set} (a : A) (P : A → Set) : A → Set where
      here : (a +> P) a
      there : ∀ {a'} → P a' → (a +> P) a'

-- #######
record Setoid : Set where
  field
    Ob : Set
    Eq : Ob → Ob → Set
open Setoid public

-- setoid with propositional equality
module _ where
  data EqPreq {A : Set} (a : A) : A → Set where
    refl : EqPreq a a

  Preq# : Set → Setoid
  Ob (Preq# A) = A
  Eq (Preq# A) = EqPreq {A}

-- setoid of setoids
module _ where
  record Iso (A B : Set) : Set where

  Setoid# : Setoid
  Setoid# = {!!}

-- setoid of arrows
module _ where
  Arrow# : Setoid → Setoid → Setoid
  Arrow# = {!!}

Pred# : Setoid → Setoid
Pred# S = Arrow# S Setoid#

{-
-- example: stlc
module _ (Θ : Set) where
  -- type
  module _ where
    data ObType : Set where
      atom : Θ → ObType
      _⇒_ : ObType → ObType → ObType

    Type# : Setoid
    Type# = Preq# ObType

  -- context
  module _ where
    ObCtx : Set
    ObCtx = ObType → Set

    Ctx# : Setoid
    Ctx# = Pred# Type#

  data Lam : ObCtx → ObType → Set where
    var : ∀ {Γ τ} → Γ τ → Lam Γ τ
    app : ∀ {Γ σ τ} → Lam Γ (σ ⇒ τ) → Lam Γ σ → Lam Γ τ
    lam : ∀ {Γ σ τ} → Lam (σ +> Γ) τ → Lam Γ (σ ⇒ τ)

  Eq2 : {Γ Γ' : ObCtx} → 
-}

-- example: untyped lambda calculus
module _ where
  -- context
  Ctx# : Setoid
  Ctx# = Setoid#

  data Lam : Set → Set where
    var : ∀ {Γ} → Γ → Lam Γ
    app : ∀ {Γ} → Lam Γ → Lam Γ → Lam Γ
    lam : ∀ {Γ} → Lam (Maybe Γ) → Lam Γ

  {-
  Γ → M Γ
  (A → B) → (M A → M B)
  -}

  mapLam : ∀ {Γ₁ Γ₂} → (Γ₁ → Γ₂) → (Lam Γ₁ → Lam Γ₂)
  mapLam f (var x) = var (f x)
  mapLam f (app s t) = app (mapLam f s) (mapLam f t)
  mapLam f (lam s) = lam (mapLam (mapMaybe f) s)

  bind : ∀ {Γ₁ Γ₂} → Lam Γ₁ → (Γ₁ → Lam Γ₂) → Lam Γ₂
  bind (var x) f = f x
  bind (app s t) f = app (bind s f) (bind t f)
  bind (lam s) f = lam (bind s \{ nothing → var nothing ; (just x) → mapLam just (f x) })

  data _→!_ {Γ : Set} : Lam Γ → Lam Γ → Set where
    β : ∀ {s t} → app (lam s) t →! {!!}

module _ where
  Map : (Set → Set) → Set
  Map F = ∀ {A B} → (A → B) → (F A → F B)

  -- free monad
  module _ (F : Set → Set) (mapF : Map F) where
    {-# NO_POSITIVITY_CHECK #-}
    data Free : Set → Set where
      pure : ∀ {A} → A → Free A
      roll : ∀ {A} → F (Free A) → Free A

    {-# TERMINATING #-}
    mapFree : Map Free
    mapFree f (pure a) = pure (f a)
    mapFree f (roll r) = roll (mapF (mapFree f) r)

    {-# TERMINATING #-}
    apFree : ∀ {A B} → Free A → Free B → Free (A × B)
    apFree (pure a) t = mapFree (\b → a & b) t
    apFree (roll r) t = roll (mapF (\s → apFree s t) r)

    -- (X → T Y) → (F X → F (T Y))
    {-# TERMINATING #-}
    bindFree : ∀ {A B} → (A → Free B) → (Free A → Free B)
    bindFree f (pure x) = f x
    bindFree f (roll r) = roll (mapF (bindFree f) r)

    -- (X → Y) → (F X → F Y)
    -- (T (T X) → T X) → (F (T (T X)) → F (T X))
    {-# TERMINATING #-}
    joinFree : ∀ {A} → Free (Free A) → Free A
    joinFree (pure t) = t
    joinFree (roll r) = roll (mapF joinFree r)

  --
  module _ (F : Set → Set) (mapF : ∀ {A B} → (A → B) → (F A → F B)) where
    data T : Set → Set where
      pure : ∀ {A} → A → T A
      roll : ∀ {A} → T (F A) → T A

    -- (U X → V Y) → (F (U X) → F (V Y))
    -- (U X → V Y) → (U (F X) → V (F Y))

    mapT : ∀ {A B : Set} → (A → B) → (T A → T B)
    mapT f (pure x) = pure (f x)
    mapT f (roll r) = roll (mapT (mapF f) r)

    postulate ff : ∀ {A B} → (A → T B) → (F A → T (F B))
    bindT : ∀ {A B} → (A → T B) → (T A → T B)
    bindT f (pure x) = f x
    bindT f (roll r) = roll (bindT (ff f) r)

    -- (∀X. X → TX) → (∀XY. (X → Y) → (TX → TY)) → Maybe (T A) → T (Maybe A)
    -- X → TX
    -- TX → T(FX)
    postulate jf : ∀ {A} → F (T A) → T (F A)
    {-# TERMINATING #-}
    joinT : ∀ {A} → T (T A) → T A
    joinT (pure t) = t
    joinT (roll r) = roll (joinT (mapT jf r))
