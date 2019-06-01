-- stlc strong normalization
module _ where

module _ where
  -- function
  module _ where
    _€_ : {A B : Set} → A → (A → B) → B
    x € f = f x

  -- rel
  module _ where
    Rel : Set → Set₁
    Rel A = A → A → Set

    data TrCl {A : Set} (R : Rel A) : Rel A where
      incl : ∀ {a b} → R a b → TrCl R a b
      ε : ∀ {a} → TrCl R a a
      _,_ : ∀ {a b c} → R a b → TrCl R b c → TrCl R a c

  module _ where
    record InfRed {A : Set} (R : Rel A) (this : A) : Set where
      coinductive
      field
        next : A
        step : R this next
        tail : InfRed R next

  module _ where
    data ⊥ : Set where

    infixr 10 _+_
    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    either : {A B X : Set} → (A → X) → (B → X) → A + B → X
    either f g (inl a) = f a
    either f g (inr b) = g b

    mapEitherL : {A A' B : Set} → (f : A → A') → A + B → A' + B
    mapEitherL f (inl x) = inl (f x)
    mapEitherL f (inr x) = inr x

  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

    add : ℕ → ℕ → ℕ
    add zero m = m
    add (succ n) m = succ (add n m)

    max : ℕ → ℕ → ℕ
    max zero m = m
    max n@(succ _) zero = n
    max (succ n) (succ m) = succ (max n m)

  -- list
  module _ where
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

    _++_ : {A : Set} → List A → List A → List A
    ε ++ ys = ys
    (x , xs) ++ ys = x , (xs ++ ys)

    data All {A : Set} : List A → (A → Set) → Set where
      ε : ∀ {P} → All ε P
      _,_ : ∀ {P a as} → P a → All as P → All (a , as) P

    mapAll : {A : Set} {P Q : A → Set} {as : List A} → (f : ∀ {xs} → P xs → Q xs) → All as P → All as Q
    mapAll f ε = ε
    mapAll f (Pa , Pas) = f Pa , mapAll f Pas

    data All2f {A : Set} {P : A → Set} (P2 : {a : A} → P a → Set) : {as : List A} → All as P → Set where
      ε : All2f P2 ε
      _,_ : ∀ {a as} {Pa : P a} {Pas : All as P} → P2 Pa → All2f P2 Pas → All2f P2 (Pa , Pas)

    data _∈_ {A : Set} : A → List A → Set where
      here : ∀ {a as} → a ∈ (a , as)
      there : ∀ {a a' as} → a ∈ as → a ∈ (a' , as)

    all : ∀ {A as P} → ({a : A} → a ∈ as → P a) → All as P
    all {as = ε} f = ε
    all {as = x , as} f = f here , all (λ {a} z → f (there z))

    get : ∀ {A as P} {a : A} → All as P → a ∈ as → P a
    get (x , x₁) here = x
    get (x , x₂) (there x₁) = get x₂ x₁

    --get2 : ∀ {A as P} {a : A} → All2f P2 as → a ∈ as → P a
    get2 : {!!}
    get2 = {!!}


  module _ where
    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just : A → Maybe A

  module _ where
    data Fin : ℕ → Set where
      zero : {n : ℕ} → Fin n
      succ : {n : ℕ} → Fin n → Fin (succ n)

module _ (Θ : Set) where
  infixr 20 _⇒_
  data Type : Set where
    atom : Θ → Type
    _⇒_ : Type → Type → Type

  size : Type → ℕ
  size (atom x) = zero
  size (s ⇒ t) = succ (add (size s) (size t))

  height : Type → ℕ
  height (atom x) = zero
  height (s ⇒ t) = succ (max (height s) (height t))

  infix 25 $_
  infixr 15 _∙_
  infix 10 ƛ_
  data Lam : List Type → Type → Set where
    $_ : ∀ {ts t} → t ∈ ts → Lam ts t
    _∙_ : ∀ {ts s t} → Lam ts (s ⇒ t) → Lam ts s → Lam ts t
    ƛ_ : ∀ {ts s t} → Lam (s , ts) t → Lam ts (s ⇒ t)

  mapLam : ∀ {t ts₁ ts₂} → (∀ {t'} → t' ∈ ts₁ → t' ∈ ts₂) → Lam ts₁ t → Lam ts₂ t
  mapLam f ($ i) = $ f i
  mapLam f (m ∙ n) = mapLam f m ∙ mapLam f n
  mapLam f (ƛ m) = ƛ mapLam (\{ here → here ; (there i) → there (f i)}) m 

  !_ : ∀ {t t' ts} → Lam ts t → Lam (t' , ts) t
  ! m = mapLam there m

  Valuation : List Type → List Type → Set
  Valuation ts₁ ts₂ = ∀ {t'} → t' ∈ ts₁ → Lam ts₂ t'

  extendVal : ∀ {ts₁ ts₂ t} → Valuation ts₁ ts₂ → Lam ts₂ t → Valuation (t , ts₁) ts₂
  extendVal ρ M here = M
  extendVal ρ M (there x) = ρ x

  -- M,ρ ↦ ⟦M⟧_ρ
  --bind : ∀ {t ts₁ ts₂} → Lam ts₁ t → (∀ {t'} → t' ∈ ts₁ → Lam ts₂ t') → Lam ts₂ t
  bind : ∀ {t ts₁ ts₂} → (M : Lam ts₁ t) → (ρ : Valuation ts₁ ts₂) → Lam ts₂ t
  bind ($ x) f = f x
  bind (m ∙ n) f = bind m f ∙ bind n f
  bind (ƛ m) f = ƛ bind m \{ here → $ here ; (there i) → mapLam there (f i) }

  infixr 15 _#_
  _#_ : ∀ {ts s t} → Lam (s , ts) t → Lam ts s → Lam ts t
  m # n = bind m \{ here → n ; (there i) → $ i } 

  infix 10 _⇛_
  data _⇛_ {ts t} : Rel (Lam ts t) where
    β : ∀ {s} {M : Lam (s , ts) t} {N : Lam ts s} → (ƛ M) ∙ N ⇛ M # N

  bind-⇛ : ∀ {ts₁ ts₂ τ} {M N : Lam ts₁ τ} → (ρ : Valuation ts₁ ts₂) → M ⇛ N → bind M ρ ⇛ bind N ρ
  bind-⇛ ρ β = {!!}

  infixr 20 _*⇒_
  _*⇒_ : List Type → Type → Type
  ε *⇒ τ = τ
  (σ , σs) *⇒ τ = σ ⇒ (σs *⇒ τ)

  infixr 15 _∙*'_
  _∙*'_ : {σs τs : List Type} {τ : Type} → (M : Lam τs (σs *⇒ τ)) → (Ns : All σs (\σ → Lam τs σ)) → Lam τs τ
  M ∙*' ε = M
  M ∙*' (N , Ns) = (M ∙ N) ∙*' Ns

  infixr 15 _∙*_
  _∙*_ : {σs τs : List Type} {τ : Type} → (M : Lam τs (σs *⇒ τ)) → (Ns : ∀ {σ} → σ ∈ σs → Lam τs σ) → Lam τs τ
  _∙*_ {σs = ε} M Ns = M
  _∙*_ {σs = σ , σs} M Ns = (M ∙ Ns here) ∙* (\x → Ns (there x))

  -- examples
  module _ where
    identityL : ∀ {t} → Lam ε (t ⇒ t)
    identityL = ƛ $ here

    identityR : ∀ {t n} → identityL {t} ∙ n ⇛ n
    identityR = β

    composeL : ∀ {t t' t''} → Lam ε ((t ⇒ t') ⇒ (t' ⇒ t'') ⇒ (t ⇒ t''))
    composeL = ƛ ƛ ƛ var1 ∙ (var2 ∙ var0)
      where
        var0 = $ here
        var1 = $ there here
        var2 = $ there (there here)

  -- strong normalization (sorensen-urzyczyn ch.4)
  module SU where
    SN : ∀ {ts t} → Lam ts t → Set
    SN M = InfRed {!!} M → ⊥

    sn-app-to-var : ∀ {ts σs τ} → (x : (σs *⇒ τ) ∈ ts) → (Ms : All σs (\σ → Lam ts σ)) → {!!} → SN (($ x) ∙*' Ms)
    sn-app-to-var =  {!!}

    inf-red-bind : ∀ {ts₁ ts₂ t} → (M : Lam ts₁ t) → (ρ : Valuation ts₁ ts₂) → InfRed {!!} M → InfRed {!!} (bind M ρ)
    inf-red-bind = {!!}

    -- σ ↦ ⟦σ⟧ ⊆ Λ
    tval : ∀ {ts} → (t : Type) → Lam ts t → Set
    tval (atom x) m = SN m
    tval {ts} (s ⇒ t) m = {n : Lam ts s} → tval s n → tval t (m ∙ n)

    record Saturated (X : ∀ ts t → (M : Lam ts t) → Set) : Set where
      field
        in-sn : ∀ {ts t} → {M : Lam ts t} → SN M → X ts t M
        p1 : ∀ {ts σ τ} {x : (σ ⇒ τ) ∈ ts} → (M : Lam ts σ) → (snM : SN M) → X _ _ ($ x ∙ M)
        p2 : {!!}

    saturated-l1 : Saturated (\ts t → SN {ts} {t})
    saturated-l1 = {!!}

    saturated-l2 : ∀ {A B : ∀ ts t → Lam ts t → Set} → Saturated A → Saturated B → Saturated {!!}
    saturated-l2 = {!!}

    saturated-l3 : (σ : Type) → Saturated (\ts t M → tval t M)
    saturated-l3 = {!!}

    -- σ,ρ,M ↦ ρ ⊨ M : σ
    ⊨ : ∀ {ts₁ ts₂} → (σ : Type) → Valuation ts₁ ts₂ → Lam ts₁ σ → Set
    ⊨ σ ρ M = tval σ (bind M ρ) 

    -- ts,ρ ↦ ρ ⊨ ts
    ⊨val : ∀ ts₁ {ts₂} → (ρ : Valuation ts₁ ts₂) → Set
    ⊨val ts₁ ρ = {t : Type} → (x : t ∈ ts₁) → tval t (ρ x)

    -- {ts₁},τ,M ↦ ts₁ ⊨ M : τ
    ⊨all : ∀ {ts₁} → (τ : Type) → (M : Lam ts₁ τ) → Set
    ⊨all {ts₁} τ M = ∀ {ts₂} → (ρ : Valuation ts₁ ts₂) → ⊨val ts₁ ρ → ⊨ τ ρ M

    soundness : ∀ {ts τ} → (M : Lam ts τ) → ⊨all τ M
    soundness ($ x) ρ dv =  dv x
    soundness (M ∙ N) ρ dv = (soundness M ρ dv) (soundness N ρ dv)
    soundness {ts} {σ ⇒ τ} (ƛ M) ρ dv {N} dN = {!soundness {σ , ts} M (\{ here → N ; (there x) → ρ x}) (\{ here → dN ; (there x) → dv x})!}

    strong-normalization : ∀ {ts t} → (M : Lam ts t) → SN M
    strong-normalization M = {!soundness M (\x → $ x)!}

  -- dexter kozen
  module dk where
    Valuation' : List Type → List Type → Set
    Valuation' ts₁ ts₂ = All ts₁ (\t → Lam ts₂ t)

    binda : ∀ {t ts₁ ts₂} → (M : Lam ts₁ t) → (ρ : Valuation' ts₁ ts₂) → Lam ts₂ t
    binda ($ x) f = get f x
    binda (m ∙ n) f = binda m f ∙ binda n f
    binda (ƛ m) f = ƛ binda m ($ here , mapAll (mapLam there) f)

    inListSum : {A : Set} → {bs : List A} {a : A} → (as : List A) → a ∈ (as ++ bs) → a ∈ as + a ∈ bs
    inListSum ε i = inr i
    inListSum (a , as) here = inl here
    inListSum (a , as) (there i) = mapEitherL there (inListSum as i)

    all++ : ∀ {A} {bs : List A} {P : A → Set} → (as : List A) → All as P → All bs P → All (as ++ bs) P
    all++ _ ε Pbs = Pbs
    all++ _ (x , Pas) Pbs = x , all++ _ Pas Pbs

    -- M (A + B) → (A → M B) → M B
    bindap : ∀ {t ts₁ ts₂} → (M : Lam (ts₁ ++ ts₂) t) → (ρ : Valuation' ts₁ ts₂) → Lam ts₂ t
    bindap {ts₁ = ts₁} e f = binda e (all++ ts₁ f (all (\i → $ i)))

    Red : ∀ {Γ τ} → Rel (Lam Γ τ)
    Red = {!!}

    SN : ∀ {ts t} → Lam ts t → Set
    SN M = InfRed Red M → ⊥

    data Args (σs : List Type) (τ : Type) : Type → Set where
      args : Args σs τ (σs *⇒ τ)

    fromArgs : ∀ {ts σs τ τ'} → Args σs τ τ' → Lam ts (σs *⇒ τ) → Lam ts τ'
    fromArgs args e = e

    toArgs : ∀ {ts σs τ τ'} → Args σs τ τ' → Lam ts τ' → Lam ts (σs *⇒ τ)
    toArgs args e = e

    {-
    {-# NO_POSITIVITY_CHECK #-}
    data USN {ts τ'} (e : Lam ts τ') : Set where
      usn : (∀ {σs τ} → {r : Args σs τ τ'} → (es : All σs (\σ → Lam ts σ)) → All2f USN es → SN (toArgs r e ∙*' es)) → USN e
      -}

    {-# NO_POSITIVITY_CHECK #-}
    record USN {ts τ'} (e : Lam ts τ') : Set where
      field usn : ∀ {σs τ} → (r : Args σs τ τ') → (es : All σs (\σ → Lam ts σ)) → (usnes : All2f USN es) → SN (toArgs r e ∙*' es)
    open USN public

    lem : ∀ {Γ τ σs} → (e : Lam (σs ++ Γ) τ) → (ds : Valuation' σs Γ) → (usnds : All2f USN ds) → USN (bindap e ds)
    usn (lem {σs = ε} ($ x) ε ε) args es usnes = {!!}
    lem {σs = σ , σs} ($ here) (d , ds) (usnd , usnds) = usnd
    lem {σs = σ , σs} ($ there x) (d , ds) (usnd , usnds) = lem ($ x) ds usnds
    usn (lem {Γ = Γ} {σs = σs} (_∙_ {s = σ} e₁ e₂) ds usnds) {σs = τs} args es usnes = usn (lem {Γ} e₁ ds usnds) (args {σs = σ , τs}) (bindap e₂ ds , es) (lem {Γ = Γ} e₂ ds usnds , usnes)
    usn (lem {Γ = Γ} {σs = σs} (ƛ_ {s = σ} {t = τ} e) ds usnds) {σs = τs} r es usnes = {!lem {Γ = σ , Γ} {σs = σs} e*!}
      where
        e* : Lam (σs ++ (σ , Γ)) τ
        e* = {!e!}

        lem1 : (d' : Lam Γ σ) → (usnd' : USN d') → USN (bindap e (d' , ds))
        lem1 d' usnd' = lem {Γ = Γ} e (d' , ds) (usnd' , usnds)
