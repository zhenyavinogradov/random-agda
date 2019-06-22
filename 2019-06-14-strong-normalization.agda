module _ where

module _ where
  -- types
  module _ where
    data ⊥ : Set where

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        fst : A
        snd : B
    open _×_ public
  
    data List (A : Set) : Set where
      ε : List A
      _∷_ : A → List A → List A

  -- function
  module _ where
    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    (f ∘ g) a = f (g a)

    identity : (A : Set) → A → A
    identity A a = a

    _€_ : {A B : Set} → A → (A → B) → B
    x € f = f x

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
    
    mapAll2 : {A : Set} {P : A → Set} {P2 Q2 : {a : A} → P a → Set} → ({a : A} → (Pa : P a) → P2 Pa → Q2 Pa) → {as : List A} → {Ps : All P as} → All2 P2 Ps → All2 Q2 Ps
    mapAll2 f ε = ε
    mapAll2 f (P2P ∷ P2Ps) = f _ P2P ∷ mapAll2 f P2Ps


  -- iso
  module _ where
    data _≡_ {A : Set} (a : A) : A → Set where
      refl : a ≡ a

    ≡-compose : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    ≡-compose refl refl = refl

    ≡-sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
    ≡-sym refl = refl

    Eq2 : {A B : Set} → (A → B) → (A → B) → Set
    Eq2 {A = A} f g = (a : A) → f a ≡ g a

    record Iso (A B : Set) : Set where
      constructor mkIso
      field
        to : A → B
        from : B → A
        to∘from : Eq2 (to ∘ from) (identity B)
        from∘to : Eq2 (from ∘ to) (identity A)
    open Iso public

  -- pred
  module _ where
    Pred : Set → Set₁
    Pred A = A → Set

    {-
    _⊆_ : {A : Set} → Pred A → Pred A → Set
    P ⊆ Q = ∀ {a} → P a → Q a
    -}

    record _⊆_ {A : Set} (P : Pred A) (Q : Pred A) : Set where
      constructor mkSub
      field sub : ∀ {a} → P a → Q a
    open _⊆_ public

    ⊆identity : {A : Set} → (P : Pred A) → P ⊆ P
    sub (⊆identity P) Pa = Pa

    ⊆compose : {A : Set} → {P Q R : Pred A} → P ⊆ Q → Q ⊆ R → P ⊆ R
    sub (⊆compose P⊆Q Q⊆R) Pa = sub Q⊆R (sub P⊆Q Pa)

    -- Eq⊆ : ∀ {A} → {P Q : Pred A} → P ⊆ Q → P ⊆ Q → Set
    -- Eq⊆ {P = P} R R' = ∀ {a} → (Pa : P a) → sub R Pa ≡ sub R' Pa
    record Eq⊆ {A : Set} {P Q : Pred A} (F G : P ⊆ Q) : Set where
      constructor mkEqSub
      field eqSub : ∀ {a} → (Pa : P a) → sub F Pa ≡ sub G Pa
    open Eq⊆ public

    Eq⊆-identity : ∀ {A} {P Q : Pred A} → (F : P ⊆ Q) → Eq⊆ F F
    eqSub (Eq⊆-identity F) Pa = refl

    Eq⊆-compose : ∀ {A} {P Q : Pred A} {F G H : P ⊆ Q} → Eq⊆ F G → Eq⊆ G H → Eq⊆ F H
    eqSub (Eq⊆-compose F=G G=H) Pa = ≡-compose (eqSub F=G Pa) (eqSub G=H Pa)

    Eq⊆-sym : ∀ {A} {P Q : Pred A} {F G : P ⊆ Q} → Eq⊆ F G → Eq⊆ G F
    eqSub (Eq⊆-sym F=G) Pa = ≡-sym (eqSub F=G Pa)

    record IsoPred {A : Set} (P Q : A → Set) : Set where
      constructor mkIsoPred
      field
        toP : P ⊆ Q
        fromP : Q ⊆ P
        to∘fromP : Eq⊆ (⊆compose fromP toP) (⊆identity Q)
        from∘toP : Eq⊆ (⊆compose toP fromP) (⊆identity P)
    open IsoPred public

    data _<+_ {A : Set} (a : A) (P : A → Set) : A → Set where
      here : (a <+ P) a
      there : ∀ {a'} → P a' → (a <+ P) a'

    _⊆<+_ : ∀ {A} → (a : A) → {P Q : A → Set} → P ⊆ Q → (a <+ P) ⊆ (a <+ Q)
    sub (a ⊆<+ F) here = here
    sub (a ⊆<+ F) (there i) = there (sub F i)

    eq-there : ∀ {A : Set} {P : Pred A} {a a' : A} {i i' : P a'} → i ≡ i' → _≡_ {(a <+ P) a'} (there i) (there i')
    eq-there refl = refl

    _=⊆<+_ : ∀ {A} → (a : A) → {P Q : A → Set} {f g : P ⊆ Q} → Eq⊆ f g → Eq⊆ (a ⊆<+ f) (a ⊆<+ g)
    eqSub (a =⊆<+ eq) here = refl
    eqSub (a =⊆<+ eq) (there x) = eq-there (eqSub eq x)

    data _<+>_ {A : Set} (P Q : A → Set) (a : A) : Set where
      inl : P a → (P <+> Q) a
      inr : Q a → (P <+> Q) a


-- ##########
module _ (Θ : Set) where
  data Type : Set where
    atom : Θ → Type
    _⇒_ : Type → Type → Type

  Context : Set₁
  Context = Type → Set

  EqCtx : Context → Context → Set
  EqCtx Γ Δ = IsoPred Γ Δ

  data Lam : Context → Type → Set where
    var : ∀ {Γ τ} → Γ τ → Lam Γ τ
    app : ∀ {Γ σ τ} → Lam Γ (σ ⇒ τ) → Lam Γ σ → Lam Γ τ
    abs : ∀ {Γ σ τ} → Lam (σ <+ Γ) τ → Lam Γ (σ ⇒ τ)

  eq-var : ∀ {Γ τ} → {x x' : Γ τ} → x ≡ x' → var {Γ} x ≡ var {Γ} x'
  eq-var refl = refl

  eq-app : ∀ {Γ σ τ} → {e₁ e₁' : Lam Γ (σ ⇒ τ)} → {e₂ e₂' : Lam Γ σ} → e₁ ≡ e₁' → e₂ ≡ e₂' → app e₁ e₂ ≡ app e₁' e₂'
  eq-app refl refl = refl

  eq-abs : ∀ {Γ σ τ} → {e e' : Lam (σ <+ Γ) τ} → e ≡ e' → abs e ≡ abs e'
  eq-abs refl = refl

  varS : ∀ {Γ} → Γ ⊆ Lam Γ
  varS = mkSub var

  mapLam : ∀ {Γ Δ} → Γ ⊆ Δ → Lam Γ ⊆ Lam Δ
  sub (mapLam f) (var x) = var (sub f x)
  sub (mapLam f) (app e e') = app (sub (mapLam f) e) (sub (mapLam f) e')
  sub (mapLam f) (abs e) = abs (sub (mapLam (_ ⊆<+ f)) e)

  -- ⊆identity: ∀ τ → Γ τ → Γ τ
  -- f : Γ τ → Γ τ
  -- f = ⊆identity
  -- (Γτ : Γ τ) → EqSet (f Γτ) Γτ

  mapLamIdentity
    : ∀ {Γ}
    → (f : Γ ⊆ Γ)
    → (_ : Eq⊆ f (⊆identity Γ))
    → Eq⊆ (mapLam f) (⊆identity (Lam Γ))
  eqSub (mapLamIdentity f f-id) (var x) = eq-var (eqSub f-id x)
  eqSub (mapLamIdentity f f-id) (app e₁ e₂) = eq-app (eqSub (mapLamIdentity f f-id) e₁) (eqSub (mapLamIdentity f f-id) e₂)
  eqSub (mapLamIdentity f f-id) (abs {σ = σ} e) = eq-abs (eqSub (mapLamIdentity (σ ⊆<+ f) (lem f f-id)) e)
    where
      lem
        : {A : Set} {a : A} {P : Pred A}
        → (f : P ⊆ P)
        → (_ : Eq⊆ f (⊆identity P))
        → Eq⊆ (a ⊆<+ f) (⊆identity (a <+ P))
      eqSub (lem f f-id) here = refl
      eqSub (lem f f-id) (there Pa) = eq-there (eqSub f-id Pa)

  mapLamCompose
    : ∀ {Γ Δ Ω}
    → (f : Γ ⊆ Δ) → (g : Δ ⊆ Ω) → (g∘f : Γ ⊆ Ω)
    → (_ : Eq⊆ g∘f (⊆compose f g))
    → Eq⊆ (mapLam g∘f) (⊆compose (mapLam f) (mapLam g))
  eqSub (mapLamCompose f g g∘f g∘f-cmp) (var x) = eq-var (eqSub g∘f-cmp x)
  eqSub (mapLamCompose f g g∘f g∘f-cmp) (app e₁ e₂) = eq-app (eqSub (mapLamCompose f g g∘f g∘f-cmp) e₁) (eqSub (mapLamCompose f g g∘f g∘f-cmp) e₂)
  eqSub (mapLamCompose f g g∘f g∘f-cmp) (abs {σ = σ} e) = eq-abs (eqSub (mapLamCompose (σ ⊆<+ f) (σ ⊆<+ g) (σ ⊆<+ g∘f) (lem f g g∘f g∘f-cmp)) e)
    where
      lem
        : {A : Set} {a : A} {P Q R : Pred A}
        → (f : P ⊆ Q) → (g : Q ⊆ R) (g∘f : P ⊆ R)
        → (_ : Eq⊆ g∘f (⊆compose {_} {P} {Q} {R} f g))
        → Eq⊆ (a ⊆<+ g∘f) (⊆compose {_} {a <+ P} {a <+ Q} {a <+ R} (a ⊆<+ f) (a ⊆<+ g))
      eqSub (lem f g g∘f eq) here = refl
      eqSub (lem f g g∘f eq) (there Pa) = eq-there (eqSub eq Pa)

  mapLamCong : ∀ {Γ Δ} {f g : Γ ⊆ Δ} → (Eq⊆ f g) → Eq⊆ (mapLam f) (mapLam g)
  eqSub (mapLamCong eq) (var x) = eq-var (eqSub eq x)
  eqSub (mapLamCong eq) (app e₁ e₂) = eq-app (eqSub (mapLamCong eq) e₁) (eqSub (mapLamCong eq) e₂)
  eqSub (mapLamCong eq) (abs e) = eq-abs (eqSub (mapLamCong (_ =⊆<+ eq)) e)

  isoLam : ∀ Γ Δ → IsoPred Γ Δ → IsoPred (Lam Γ) (Lam Δ)
  isoLam Γ Δ (mkIsoPred to' from' to∘from' from∘to') = mkIsoPred (mapLam to') (mapLam from') to∘from* from∘to*
    where
      to∘from* : Eq⊆ (⊆compose (mapLam from') (mapLam to')) (⊆identity (Lam Δ))
      to∘from* =
        Eq⊆-compose {G = mapLam (⊆compose from' to')}
          (Eq⊆-sym (mapLamCompose from' to' (⊆compose from' to') (Eq⊆-identity _)))
        (Eq⊆-compose {G = mapLam (⊆identity Δ)}
          (mapLamCong to∘from')
          (mapLamIdentity (⊆identity Δ) (Eq⊆-identity _))
        )

      from∘to* : Eq⊆ (⊆compose (mapLam to') (mapLam from')) (⊆identity (Lam Γ))
      from∘to* =
        Eq⊆-compose {G = mapLam (⊆compose to' from')}
          (Eq⊆-sym (mapLamCompose to' from' (⊆compose to' from') (Eq⊆-identity _)))
        (Eq⊆-compose {G = mapLam (⊆identity Γ)}
          (mapLamCong from∘to')
          (mapLamIdentity (⊆identity Γ) (Eq⊆-identity _))
        )
  binds : ∀ {Γ Δ τ} → Lam Γ τ → (Γ ⊆ Lam Δ) → Lam Δ τ
  binds (var x) ds = sub ds x
  binds (app e e') ds = app (binds e ds) (binds e' ds)
  binds (abs e) ds = abs (binds e (mkSub \{ here → var here ; (there x) → sub (mapLam (mkSub there)) (sub ds x) }))

  -- Γ ⊆ Lam Γ
  -- (Γ ⊆ Δ) → (Lam Γ ⊆ Lam Δ)
  -- Γ ⊆ Lam Δ
  -- σ <+ Γ ⊆ Lam (σ <+ Δ)

  traverse : ∀ {Γ Δ σ} → Γ ⊆ Lam Δ → (σ <+ Γ) ⊆ Lam (σ <+ Δ)
  sub (traverse ds) here = var here
  sub (traverse ds) (there x) = sub (mapLam (mkSub there)) (sub ds x)

  binds' : ∀ {Γ Δ} → (Γ ⊆ Lam Δ) → (Lam Γ ⊆ Lam Δ)
  sub (binds' ds) (var x) = sub ds x
  sub (binds' ds) (app e e') = app (sub (binds' ds) e) (sub (binds' ds) e')
  sub (binds' ds) (abs e) = abs (sub (binds' (traverse ds)) e)

  bindsa : ∀ {Γ Γ' τ} → Lam (Γ' <+> Γ) τ → (Γ' ⊆ Lam Γ) → Lam Γ τ
  bindsa e ds = binds e (mkSub \{ (inl x) → sub ds x ; (inr y) → var y })

  ⊆-pair : {A : Set} → {P Q R : Pred A} → P ⊆ R → Q ⊆ R → (P <+> Q) ⊆ R
  sub (⊆-pair P⊆R Q⊆R) (inl Pa) = sub P⊆R Pa
  sub (⊆-pair P⊆R Q⊆R) (inr Qa) = sub Q⊆R Qa

  bindsa' : ∀ {Γ Γ'} → (Γ' ⊆ Lam Γ) → (Lam (Γ' <+> Γ) ⊆ Lam Γ)
  -- bindsa' ds = binds' (mkSub \{ (inl x) → sub ds x ; (inr y) → var y })
  bindsa' ds = binds' (⊆-pair ds (mkSub var))

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

  usn⇒sn : ∀ {Γ τ} → (e : Lam Γ τ) → USN e → SN e
  usn⇒sn {Γ} {τ} e usne = usn usne ε τ args ε ε  

  usn-iso : ∀ {Γ Δ τ} → (iso : IsoPred Γ Δ) → (e : Lam Γ τ) → USN e → USN (sub (toP (isoLam _ _ iso)) e)
  usn-iso = {!!}

  All2P : {A : Set} (P : A → Set) {Q : A → Set} → (Q2 : {a : A} → Q a → Set) → (F : P ⊆ Q) → Set
  All2P {A} P Q2 F = {a : A} → (Pa : P a) → Q2 (sub F Pa)

  sn-app-var : ∀ {Γ σs τ} → (x : Γ (σs *⇒ τ)) → (es : All (Lam Γ) σs) → All2 SN es → SN (app* (var x) es)
  sn-app-var = {!!}

  sn-lam : ∀ {Γ σ τ} → (e : Lam (σ <+ Γ) τ) → SN e → SN (abs e)
  sn-lam = {!!}

  -- lem : ∀ Γ σs τ → (e : Lam (σs <+> Γ) τ) → (ds : σs ⊆ Lam Γ) → (usnds : All2P σs USN ds) → USN (bindsa e ds)
  lem : ∀ Γ σs τ → (e : Lam (σs <+> Γ) τ) → (ds : σs ⊆ Lam Γ) → (usnds : All2P σs USN ds) → USN (sub (bindsa' ds) e)
  lem Γ σs τ (var (inl x)) ds usnds = usnds x
  usn (lem Γ σs .(τs *⇒ τ) (var (inr x)) ds usnds) τs τ args es usnes = sn-app-var x es (mapAll2 usn⇒sn usnes)
  usn (lem Γ σs .(τs *⇒ τ) (app {σ = σ} e₁ e₂) ds usnds) τs τ args es usnes = usn (lem Γ σs _ e₁ ds usnds) (σ ∷ τs) τ args (sub (bindsa' ds) e₂ ∷ es) (lem Γ σs _ e₂ ds usnds ∷ usnes)
  usn (lem Γ σs .(σ ⇒ τ) (abs {σ = σ} {τ = τ} e) ds usnds) .ε .(σ ⇒ τ) args ε ε = sn-lam _ sn-esub
    where
      iso1 : IsoPred (σ <+ (σs <+> Γ)) (σs <+> (σ <+ Γ))
      iso1 = {!!}

      lem1 : USN (sub (bindsa' (⊆compose ds (mapLam (mkSub there)))) (sub (toP (isoLam _ _ iso1)) e))
      lem1 = {!!}

      esub : Lam (σ <+ Γ) τ
      esub = sub (binds' (traverse (⊆-pair ds (mkSub var)))) e

      esub' : Lam (σs <+> (σ <+ Γ)) τ
      esub' = {!!}

      usn-esub' : USN esub'
      usn-esub' = {!lem!}

      usn-esub : USN esub
      usn-esub = {!!}

      sn-esub : SN esub
      sn-esub = usn⇒sn _ usn-esub
  usn (lem Γ σs .(σ ⇒ (τs *⇒ τ)) (abs {σ = σ} e) ds usnds) (σ ∷ τs) τ args (e₁ ∷ es) (usne₁ ∷ usnes) = {!!}
