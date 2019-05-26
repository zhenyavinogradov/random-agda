-- random algebraic definitions
{-# OPTIONS --type-in-type #-}
module _ where

-- lib
module _ where
  -- function
  module _ where
    identity : {A : Set} → A → A
    identity x = x

    compose : {A B C : Set} → (A → B) → (B → C) → (A → C)
    compose f g a = g (f a)

  -- finite (co)product
  module _ where
    data ⊥ : Set where

    bottom : {A : Set} → ⊥ → A
    bottom ()

    record ⊤ : Set where
      constructor tt

    top : {A : Set} → A → ⊤
    top a = tt

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    either : {A B C : Set} → (A → C) → (B → C) → (A + B → C)
    either f g (inl a) = f a
    either f g (inr b) = g b

    record _×_ (A B : Set) : Set where
      constructor _&_
      field
        fst : A
        snd : B
    open _×_ public

    cross : {A B X : Set} → (X → A) → (X → B) → (X → A × B)
    cross f g x = f x & g x

  -- list
  module _ where
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

-- monad
module _ where
  record SetMonad (M : Set → Set) : Set where
    field
      map : {A B : Set} → (A → B) → (M A → M B)
      pure : {A : Set} → A → M A
      join : {A : Set} → M (M A) → M A

  module _ (M : Set → Set) (IsSetMonadM : SetMonad M) where
    open SetMonad IsSetMonadM

    _>>=_ : {A B : Set} → M A → (A → M B) → M B
    _>>=_ m f = join (map f m)

    _>>_ : {A B : Set} → M A → M B → M B
    _>>_ m m' = m >>= \_ → m'

    mconcat : List (M ⊤) → M ⊤
    mconcat ε = pure tt
    mconcat (m , ms) = m >> mconcat ms


-- predicate
module _ where
  Pred : Set → Set
  Pred A = A → Set

  infix 25 !_
  !_ : {A : Set} → Set → Pred A
  (! X) _ = X

  data Map {A B : Set} (f : A → B) (P : Pred A) : Pred B where
     mapPred : {a : A} → P a → Map f P (f a)

  data Pure {A : Set} (a : A) : Pred A where
     purePred : Pure a a

  data Join {A : Set} (Q : Pred (Pred A)) : Pred A where
    joinPred : {P : Pred A} {a : A} → Q P → P a → Join Q a

  module _ where
    infixr 5 _<→>_
    _<→>_ : {A B : Set} → Pred A → Pred B → Pred (A → B)
    (P <→> Q) f = ∀ {a} → P a → Q (f a)
    
    _⊆_ : {A : Set} → Pred A → Pred A → Set
    P ⊆ Q = (P <→> Q) identity

    identityP : ∀ {A : Set} {P : Pred A} → (P <→> P) identity
    identityP pa = pa

    composeP : ∀ {A B C : Set} {P : Pred A} {Q : Pred B} {R : Pred C} → ((P <→> Q) <→> ((Q <→> R) <→> (P <→> R))) compose
    composeP P→fQ Q→gR Pa = Q→gR (P→fQ Pa)

  module _ where
    infixr 5 _<←>_
    _<←>_ : {A B : Set} → Pred A → Pred B → Pred (A → B)
    (Q <←> P) f = ∀ {a} → P (f a) → Q a

  -- ⊥ and ⊤
  module _ where
    module _ where
      ⊥P : Pred ⊥
      ⊥P _ = ⊥

      -- ⊥ → A
      bottomP : ∀ {A} {P : Pred A} → (⊥P <→> P) bottom
      bottomP ()

      -- ⊥ → A
      bottomP' : ∀ {A} {P : Pred A} → (⊥P <←> P) bottom
      bottomP' {a = ()}

    module _ where
      ⊤P : Pred ⊤
      ⊤P tt = ⊤

      -- A → ⊤
      topP : ∀ {A} {P : Pred A} → (P <→> ⊤P) top
      topP Pa = tt

    module _ where
      ⊤P' : Pred ⊤
      ⊤P' tt = ⊥

      -- A → ⊤
      topP' : ∀ {A} {P : Pred A} → (P <←> ⊤P') top
      topP' ()

  module _ where
    infixr 15 _<×>_
    _<×>_ : {A B : Set} → Pred A → Pred B → Pred (A × B)
    (P <×> Q) (a & b) = P a × Q b

    fstP : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <×> Q <→> P) fst
    fstP P×Qa = fst P×Qa

    sndP : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <×> Q <→> Q) snd
    sndP P×Qa = snd P×Qa

    pairP : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <→> Q <→> P <×> Q) _&_
    pairP Pa Qa = Pa & Qa

  module _ where
    infixr 10 _<+>_
    _<+>_ : {A B : Set} → Pred A → Pred B → Pred (A + B)
    (P <+> Q) e = either P Q e

    inlP : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <→> P <+> Q) inl
    inlP Pa = Pa

    inrP : ∀ {A B} {P : Pred A} {Q : Pred B} → (Q <→> P <+> Q) inr
    inrP Qa = Qa

    eitherP : ∀ {A B C} {P : Pred A} {Q : Pred B} {R : Pred C} → ((P <→> R) <→> (Q <→> R) <→> (P <+> Q <→> R)) either
    eitherP P→fR Q→gR {inl a} Pa = P→fR Pa
    eitherP P→fR Q→gR {inr b} Qb = Q→gR Qb

    -- A → A + B
    inlP' : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <←> P <+> Q) inl
    inlP' Pa = Pa

    -- B → A + B
    inrP' : ∀ {A B} {P : Pred A} {Q : Pred B} → (Q <←> P <+> Q) inr
    inrP' Qb = Qb

    -- (A → X) → (B → X) → (A + B → X)
    eitherP' : ∀ {A B C} {P : Pred A} {Q : Pred B} {R : Pred C} → ((P <←> R) <→> (Q <←> R) <→> (P <+> Q <←> R)) either
    eitherP' fR→P gR→Q {inl a} Rfa = fR→P Rfa
    eitherP' fR→P gR→Q {inr b} Rgb = gR→Q Rgb

  module _ where
    infixr 15 _<&>_
    _<&>_ : {A B : Set} → Pred A → Pred B → Pred (A × B)
    (P <&> Q) (a & b) = P a + Q b

    -- A × B → A
    fstP' : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <&> Q <←> P) fst
    fstP' Pa = inl Pa

    -- A × B → B
    sndP' : ∀ {A B} {P : Pred A} {Q : Pred B} → (P <&> Q <←> Q) snd
    sndP' Qb = inr Qb

    -- (X → A) → (X → B) → (X → A × B)
    crossP' : ∀ {A B C} {P : Pred A} {Q : Pred B} {R : Pred C} → ((R <←> P) <→> (R <←> Q) <→> (R <←> P <&> Q)) cross
    crossP' fP→R gQ→R (inl Pfx) = fP→R Pfx
    crossP' fP→R gQ→R (inr Qgx) = gQ→R Qgx

  -- induction and coinduction
  module _ (F : Set → Set) (mapF : ∀ {A B} → (A → B) → (F A → F B)) where
    -- induction
    module _ where
      {-# NO_POSITIVITY_CHECK #-}
      data μF : Set where
        roll : F μF → μF

      {-# TERMINATING #-}
      induction : ∀ {X} → (F X → X) → (μF → X)
      induction k (roll f) = k (mapF (induction k) f) 

      module _
          (PredF : {X : Set} → Pred X → Pred (F X))
          (mapFP : {A B : Set} {P : Pred A} {Q : Pred B} → ((P <→> Q) <→> (PredF P <→> PredF Q)) mapF)
        where

        {-# NO_POSITIVITY_CHECK #-}
        data μFP : Pred μF where
          rollP : {r : F μF} → PredF μFP r → μFP (roll r)

        {-# TERMINATING #-}
        inductionP : ∀ {X} {P : Pred X} → ((PredF P <→> P) <→> (μFP <→> P)) induction
        inductionP k (rollP Pr) = k (mapFP (inductionP k) Pr)

    -- coinductioG
    module _ where
      {-# NO_POSITIVITY_CHECK #-}
      record νF : Set where
        coinductive
        constructor ununroll
        field unroll : F νF
      open νF public

      {-# TERMINATING #-}
      coinduction : ∀ {X} → (X → F X) → (X → νF)
      unroll (coinduction k x) = mapF (coinduction k) (k x)

      module _ (PredF : {X : Set} → Pred X → Pred (F X)) where
        {-# NO_POSITIVITY_CHECK #-}
        record νFP (r : νF) : Set where
          coinductive
          field unrollP : PredF νFP (unroll r)

        {-# NO_POSITIVITY_CHECK #-}
        record νFP' (r : νF) : Set where
          inductive
          field unrollP' : PredF νFP' (unroll r)

        {-
        {-# NO_POSITIVITY_CHECK #-}
        data νFP' : Pred νF where
          ununrollP : {r : F νF} → PredF νFP' r → νFP' (ununroll r)
        -}

    -- dependent (co)product on sets
    module _ where
      record Σ (A : Set) (B : Pred A) : Set where
        constructor _&&_
        field
          first : A
          second : B first
      open Σ public

      Σ-intro : {A : Set} {B : Pred A} → B ⊆ ! Σ A B
      Σ-intro = _&&_ _

      Σ-elim : {A : Set} {B : Pred A} {X : Set} → (B ⊆ ! X) → (Σ A B → X)
      Σ-elim x x₁ = x (second x₁)

      -- Π : (A : Set) → Pred A → Set
      Π : (A : Set) → Pred (Pred A)
      Π A B = (a : A) → B a

      -- : {A : Set} {B : Pred A} → (a : A) → ! (Π A B) (t a) → B a
      Π-elim : {A : Set} {B : Pred A} → ! Π A B ⊆ B
      Π-elim {a = a} f = f a

      Π-intro : {A : Set} {B : Pred A} {X : Set} → (! X ⊆ B) → (X → Π A B)
      Π-intro = λ z z₁ a → z z₁


    -- dependent (co)product on predicates
    module _ where
      Pred1 : {A : Set} → Pred A → Pred (Pred A)
      Pred1 {A} P B = {a : A} → P a → Pred (B a)

      Pred1' : {A : Set} (B : A → Set) → ({a : A} → Pred (B a)) → Set
      Pred1' {A} B P = {a : A} → {b : B a} → P b → Pred A

      _<⊆>_ : {!!}
      S <⊆> T = {!!}

      -- pair
      module _ where
        <Σ> : {A : Set} {B : A → Set} → (P : Pred A) → (Q : Pred1 P B) → Pred (Σ A B)
        <Σ> P Q (a && b) = Σ (P a) \Pa → Q Pa b

        --Σ-introP : ∀ {A B} {P : Pred A} → (Q <⊆> ! <Σ> P Q) Σ-intro

      -- function
      module _ where
        <Π> : {A : Set} {B : A → Set} → (P : Pred A) → (Q : Pred1 P B) → Pred (Π A B)
        <Π> {A} P Q f = {a : A} → (Pa : P a) → Q Pa (f a)

        <Π'> : {A : Set} {B : A → Set} → (P : {a : A} → Pred (B a)) → (Q : {a : A} → {b : B a} → P b → Pred A) → Pred (Π A B)
        <Π'> {A} P Q f = {a : A} → (Pfa : P (f a)) → Q Pfa a
