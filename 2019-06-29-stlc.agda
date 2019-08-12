-- stlc with induction and coinduction
module _ where

module _ where
  module _ where
    data ⊥ : Set where

    record ⊤ : Set where
      constructor tt

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        fst : A
        snd : B
    open _×_ public

    data Bool : Set where
      false true : Bool

    bool : {A : Set} → A → A → Bool → A
    bool a b true = a
    bool a b false = b

    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,,_
      field
        π₁ : A
        π₂ : B π₁
    open Σ public

    data List (A : Set) : Set where
      ε : List A
      _∷_ : A → List A → List A

    postulate String : Set
    {-# BUILTIN STRING String #-}

  -- list
  module _ where
    data In {A : Set} : List A → A → Set where
      here : ∀ {a as} → In (a ∷ as) a
      there : ∀ {a a' as} → In as a → In (a' ∷ as) a

    Elem : {A : Set} → List A → Set
    Elem {A} as = Σ A \a → In as a

    data All {A : Set} (P : A → Set) : List A → Set where
      ε : All P ε
      _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

    data All2 {A : Set} {P : A → Set} (P2 : (a : A) → P a → Set) : {as : List A} → All P as → Set where
      ε : All2 P2 ε
      _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} → P2 a Pa → All2 P2 Pas → All2 P2 (Pa ∷ Pas)

    single : {A : Set} → A → List A
    single a = a ∷ ε

    get : ∀ {A : Set} {P : A → Set} {τs τ} → All P τs → In τs τ → P τ
    get = {!!}

    remove : {A : Set} {a : A} → (as : List A) → In as a → List A
    remove (a ∷ as) here = as
    remove (a ∷ as) (there i) = a ∷ remove as i

    wasThere : {A : Set} {a : A} {as : List A} {d : A} → (id : In as d) → In (remove as id) a → In as a
    wasThere here i = there i
    wasThere (there id) here = here
    wasThere (there id) (there i) = there (wasThere id i)

    mapList : {A B : Set} → (A → B) → List A → List B
    mapList f ε = ε
    mapList f (a ∷ as) = f a ∷ mapList f as

    eqIn : {A : Set} {a a' : A} {as : List A} → In as a → In as a' → Bool
    eqIn here here = true
    eqIn here (there j) = false
    eqIn (there i) here = false
    eqIn (there i) (there j) = eqIn i j

module _ where
  record Var : Set where
    field
      v : String

  Vars : Set
  Vars = List Var

  Abs : (Vars → Set) → (Vars → Set)
  Abs T vs = Σ Var \v → T (v ∷ vs)

  data Type : Vars → Set where
    var  : ∀ {vs} → Elem vs → Type vs
    σ π  : ∀ {vs} → List (Type vs) → Type vs
    μ ν  : ∀ {vs} → Abs Type vs → Type vs

  AbsType : Vars → Set
  AbsType = Abs Type

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

  _#_ : ∀ {vs} → Abs Type vs → Type vs → Type vs
  (v ,, ϕ) # τ = subst ϕ v here τ

  Ctx : Vars → Set
  Ctx tvs = List (Var × Type tvs)

  AbsT : {tvs : Vars} → (Ctx tvs → Type tvs → Set) → Ctx tvs → Type tvs → Type tvs → Set
  AbsT Tm Γ ρ τ = Σ Var (\v → Tm ((v , ρ) ∷ Γ) τ)

  {-
  Type : Set
  _⇒_ : Type → Type → Set
  _⇛_ : (A ⇒ B) → (A ⇒ B) → Set
  -}
  data Term {tvs : Vars} : Ctx tvs → Type tvs → Set where
    var : ∀ {Γ τ} → (v : Var) → In Γ (v , τ) → Term Γ τ

    -- inj : In τs τ → (τ ⇒ σ τs)
    σ-intr : ∀ {Γ τs τ} → In τs τ → Term Γ τ → Term Γ (σ τs)
    -- sum :  All (\τ → (τ ⇒ ρ)) τs → (σ τs ⇒ ρ)
    σ-elim : ∀ {Γ τs ρ} → All (\τ → AbsT Term Γ τ ρ) τs → Term Γ (σ τs) → Term Γ ρ

    -- com :  All (\τ → (ρ ⇒ τ)) τs → (ρ ⇒ π τs)
    --com : ∀ {Γ τs ρ} → All (\τ → AbsT Term Γ ρ τ) τs → Term Γ ρ → Term Γ (π τs)
    π-intr : ∀ {Γ τs} → All (\τ → Term Γ τ) τs → Term Γ (π τs)
    --π-intr : ∀ {Γ : Ctx tvs} {τs : List (Type tvs)} (ϕ : Type tvs) (ϕ ≡ π (τ₁…τₙ)) (_ : Term Γ τ₁) … (_ : Term Γ τₙ) → (τ₁ ≡ get τs 1) … (τₙ ≡ get τs n) → Term Γ ϕ
    -- prj : Elem τs τ → (π τs ⇒ τ)
    π-elim : ∀ {Γ τs τ} → In τs τ → Term Γ (π τs) → Term Γ τ

    -- con : ϕ # μ ϕ ⇒ μ ϕ
    μ-intr : ∀ {Γ ϕ} → Term Γ (ϕ # μ ϕ) → Term Γ (μ ϕ)
    -- ind : (ϕ # ρ ⇒ ρ) → (μ ϕ ⇒ ρ)
    μ-elim : ∀ {Γ ρ} ϕ → AbsT Term Γ (ϕ # ρ) ρ → Term Γ (μ ϕ) → Term Γ ρ

    -- coi : (ρ ⇒ ϕ # ρ) → (ρ ⇒ ν ρ)
    ν-intr : ∀ {Γ ρ} ϕ → AbsT Term Γ ρ (ϕ # ρ) → Term Γ ρ → Term Γ (ν ϕ)
    -- dec : ν ϕ ⇒ ϕ # ν ϕ
    ν-elim : ∀ {Γ ϕ} → Term Γ (ν ϕ) → Term Γ (ϕ # ν ϕ)

  AbsTerm : {tvs : Vars} → Ctx tvs → Type tvs → Type tvs → Set
  AbsTerm = AbsT Term

  map : ∀ {tvs} → (ϕ : AbsType tvs) → ∀ {Γ σ τ} → (Term Γ σ → Term Γ τ) → (Term Γ (ϕ # σ) → Term Γ (ϕ # τ))
  map = {!!}

  _$_ : {tvs : Vars} {Γ : Ctx tvs} {ρ τ : Type tvs} → AbsTerm Γ ρ τ → Term Γ ρ → Term Γ τ
  _$_ = {!!}

  infix 5 _⇒_
  data _⇒_ {tvs : Vars} {Γ : Ctx tvs} : {τ : Type tvs} → Term Γ τ → Term Γ τ → Set where
    -- σ-rule : sum As ∘ inj i ⇛ get As i
    σ-rule : ∀ {τ ρ τs} {As : All (\α → AbsTerm Γ α ρ) τs} {i : In τs τ} → {t : Term Γ τ} → σ-elim As (σ-intr i t) ⇒ (get As i $ t)
    -- π-rule : prj i ∘ com As ⇛ get As i
    --π-rule : ∀ {τ ρ τs} {As : All (\α → AbsTerm Γ ρ α) τs} {i : In τs τ} → ∀ {t} → π-elim i (π-intr As t) ⇒ (get As i $ t)
    π-rule : ∀ {τ τs} {As : All (\α → Term Γ α) τs} {i : In τs τ} → π-elim i (π-intr As) ⇒ get As i
    -- μ-rule : ind ϕ f ∘ con ⇛ f ∘ map ϕ (ind ϕ f)
    μ-rule : {ϕ : AbsType tvs} {ρ : Type tvs} {f : AbsTerm Γ (ϕ # ρ) ρ} → {t : Term Γ (ϕ # μ ϕ)} → μ-elim ϕ f (μ-intr t) ⇒ (f $ map ϕ (μ-elim ϕ f) t)
    -- ν-rule : dec ∘ coi ϕ f ⇛ map ϕ (coi ϕ f) ∘ f
    --ν-rule : {ϕ : AbsType tvs} {ρ : Type tvs} {f : AbsTerm Γ ρ (ϕ # ρ)} → {t : Term Γ ρ} → ν-elim (ν-intr ϕ f t) ⇒ map ϕ (ν-intr ϕ f) (f $ t)

  {-
  Type : Vars → Set
  AbsType : Vars → Set
  Context : Vars → Set
  Term : Context tvs → Type tvs → Set
  AbsTerm : Context tvs → Type tvs → Type tvs → Set
  _⇒_ : Term Γ τ → Term Γ τ → Set
  
  ⟦_⟧v : Vars → Set
  ⟦ ε ⟧v = ⊤
  ⟦ v ∷ vs ⟧v = Set × ⟦ vs ⟧v

  ⟦_⟧ : Type tvs → ⟦tvs⟧v → Set
  ⟦τᵢ⟧ → ⟦σ[τ₁…τₙ]⟧
  ⟦τ₁⟧, …, ⟦τₙ⟧ → ⟦π[τ₁…τₙ]⟧
  ⟦ϕ⟧ ⟦μϕ⟧ → ⟦μϕ⟧
  ⟦ρ⟧, (⟦ρ⟧ → ⟦ϕ⟧ ⟦ρ⟧) → ⟦νϕ⟧
  ---
  Term Γ τ → ⟦Γ⟧ → ⟦τ⟧
  
  -- turing machine
  State[Σ] = π[Stream[Σ], Stream[Σ]]
  left[Σ], right[Σ] : State[Σ] → State[Σ]
  write[Σ] : State[Σ], Σ → State[Σ]
  read[Σ] : State[Σ] → Σ
  Program[Σ,R] = νX. σ[read : Σ ⇒ X, write : Σ × X, left : X, right : X, halt : R]
  Delay[A] = νX. σ[A, X]
  step[Σ,R] : Program[Σ,R], State[Σ] → R + Program[Σ,R] × State[Σ]
  run[Σ,R] : Program[Σ,R], State[Σ] → Delay[R]
  
  --
  σ π : List Type → Type
  μ ν : Abs Type → Type

  _⇒_ : Type → Type → Type
  abs : AbsTerm Γ σ τ → Term Γ (σ ⇒ τ)
  app : Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  --
  _×_ : Type → Type → Type
  pair : Term Γ σ × Term Γ τ → Term Γ (σ × τ)
  proj : Term Γ (σ × τ) → Term Γ σ × Term Γ τ
  
  Cont[R,A] = (A ⇒ R) ⇒ R
  map[R,A] : (A ⇒ B) → (Cont[R,A] ⇒ Cont[R,B])
  _⇒[R]_[A,B] = A ⇒ Cont[R,B]
  pure[R,A] : A ⇒[R] A
  fish[R,A,B] : (A ⇒[R] B) → (B ⇒[R] C) → (A ⇒[R] C)
  bind[R,A,B] : (A ⇒ Cont[R,B]) ⇒ (Cont[R,A] ⇒ Cont[R,B])
  σCont[R,A₁…Aₙ] = Cont[R,σ[A₁…Aₙ]]
  πCont[R,A₁…Aₙ] = Cont[R,π[A₁…Aₙ]]
  ⊥Cont[R] = πCont[R][]
  doubleNegation : ((A ⇒[R] R) ⇒[R] R) ⇒[R] A
  ~ ((A⇒(R⇒R)⇒R) ⇒ (R⇒R) ⇒ R) ⇒ (A⇒R) ⇒ R
  ~: λf: (A⇒(R⇒R)⇒R) ⇒ (R⇒R) ⇒ R. λg:A⇒R. (f (λa:R. λ_:R⇒R. g a)) (λr:R. r)
  excludedMiddle : Cont[R, σ[A, A ⇒ R]]
  ~ (σ[A, A⇒R] ⇒ R) ⇒ R
  ~: λf: σ[inl: A, inr: A⇒R] ⇒ R. f (inr (λa:A. f (inl a)))
  pierceLaw : ((A ⇒[R] B) ⇒[R] A) ⇒[R] A
  ~ ((A ⇒ (B ⇒ R) ⇒ R) ⇒ (A ⇒ R) ⇒ R) ⇒ (A ⇒ R) ⇒ R
  ~: λf: (A⇒(B⇒R)⇒R) ⇒ (A⇒R) ⇒ R. λg: A⇒R. f (λa:A. λ_:B⇒R. g a) (λa. g a)
  
  ∀ : AbsType tvs → Type tvs
  ∀-intr : Term (x ∷ Θ) Γ!x ϕ → Term Θ Γ (∀x. ϕ)
  ∀-elim : (τ : Type Θ) → Term Θ Γ (∀x. ϕ) → Term Θ Γ ϕ[x/τ]
  --
  ∃ : AbsType tvs → Type tvs
  ∃-intr : (τ : Type Θ) → Term Θ Γ ϕ[x/τ] → Term Θ Γ (∃x. ϕ)
  ∃-elim : Term Θ Γ (∃x. ϕ), AbsTerm (x , Θ) Γ!x ϕ ρ!x → Term Θ Γ ρ
  
  -- higher-kinded types (F_ω)
  ⋆ : Kind
  _⇒_ : Kind → Kind → Kind
  absT : AbsType Θ κ₁ κ₂ → Type Θ (κ₁ ⇒ κ₂)
  appT : Type Θ (κ₁ ⇒ κ₂) → Type Θ κ₁ → Type Θ κ₂
  
  -- predicate logic
  FunDegree = ℕ
  FunVars = List (FunVar × FunDegree)
  Term : (fvs : FunVars) → Set
  function : (fv : FunVar) → ((fv, n) ∈ fvs) → Vec n (Term fvs) → Term fvs

  PredDegree = ℕ
  PredVars = List (PredVar × PredDegree)
  Formula : (pvs : PredVars) → (fvs : FunVars) → Set
  predicate : (pv : PredVar) → (pv , n) ∈ pvs → Vec n (Term fvs) → Formula pvs fvs
  _⇒_ : Formula pvs fvs → Formula pvs fvs → Formula pvs fvs
  σ π : List (Formula pvs fvs) → Formula pvs fvs
  ∀ ∃ : (sv : FunVar) → Formula pvs ((sv : 0 ⇒T) , fvs) → Formula pvs fvs
  
  FmlVars fvs = List (FmlVar × Formula fvs)
  T : {pvs : PredVars}, (fvs : FunVars), (Γ : FmlVars fvs) → Formula → Set
  --
  ⇒-intr : T fvs ((x, σ) ∷ Γ) τ → T fvs Γ (σ ⇒ τ)
  ⇒-elim : T fvs Γ (σ ⇒ τ) → T fvs Γ σ → T pvs fvs Γ τ
  --
  ∀-intr : T ((x, 0) ∷ fvs) Γ!x ϕ → T fvs Γ (∀x. ϕ)
  ∀-elim : T fvs Γ (∀x. ϕ) → (t : Term fvs) → T fvs Γ ϕ[x/t]
  --
  ∃-intr : (t : Term fvs) → T fvs Γ ϕ[x/t] → T fvs Γ (∃x. ϕ)
  ∃-elim : T fvs Γ (∃x. ϕ) → (a b : Var) × T ((a , 0) ∷ fvs) ((b , ϕ[x/a]) ∷ Γ) ρ!a → T fvs Γ ρ
  
  ⟦_⟧
  : FunDegree → Set
  : FunVars → Set
  : ⟦fvs⟧ → Term fvs → Set
  : PredDegree → Set
  : PredVars → Set
  : ⟦pvs⟧ → ⟦fvs⟧ → Formula pvs fvs → Set
  --
  ⟦k : FunDegree⟧ = Dᵏ → D
  ⟦fvs = (f₁, d₁), …⟧ = ⟦d₁⟧ × …
  ⟦function fᵢ (t₁…tₙ)⟧ = ⟦dᵢ⟧ (⟦t₁⟧, …, ⟦tₙ⟧)
  ⟦k : PredDegree⟧ = Dᵏ → Set
  ⟦pvs = (p₁,d₁), …⟧ = ⟦d₁⟧ × …
  ⟦predicate pᵢ (t₁…tₙ)⟧ = ⟦pᵢ⟧ (⟦t₁⟧, …, ⟦tₙ⟧)
  ⟦f ⇒ g⟧ = ⟦f⟧ → ⟦g⟧
  ⟦σ[f₁…fₙ]⟧ = ⟦f₁⟧ + … + ⟦fₙ⟧
  ⟦π[f₁…fₙ]⟧ = ⟦f₁⟧ × … × ⟦fₙ⟧
  ⟦∀x. ϕ⟧ = (d : D) → ⟦ϕ⟧[x:=d]
  ⟦∃x. ϕ⟧ = (d : D) × ⟦ϕ⟧[x:=d]
  -}
  module _ where
    valType : {tvs : Vars} → Type tvs → Set
    valType = {!!}
    valContext : {tvs : Vars} → Ctx tvs → Set
    valContext = {!!}
    valTerm : {tvs : Vars} → (Γ : Ctx tvs) → (τ : Type tvs) → Term Γ τ → valContext Γ → valType τ
    valTerm = {!!}

  Subterm : {tvs : Vars} → (∀ {Γ τ} → Term {tvs} Γ τ → Set) → (∀ {Γ τ} → Term {tvs} Γ τ → Set)
  Subterm = {!!}

  data NF {tvs} : (Γ : Ctx tvs) → (τ : Type tvs) → Term {tvs} Γ τ → Set where
    nfVar : ∀ {Γ τ v} → (x : In Γ (v , τ)) → NF Γ τ (var v x)

    --σ-intr : ∀ {Γ τs τ} → In τs τ → Term Γ τ → Term Γ (σ τs)
    nfσ : ∀ {Γ τs τ} → (i : In τs τ) → (A : Term Γ τ) → NF Γ τ A → NF Γ (σ τs) (σ-intr i A)

    --π-intr : ∀ {Γ τs} → All (\τ → Term Γ τ) τs → Term Γ (π τs)
    nfπ : ∀ {Γ τs} → (As : All (\τ → Term Γ τ) τs) → All2 (\τ A → NF Γ τ A) As → NF Γ (π τs) (π-intr As)
 
    --μ-intr : ∀ {Γ ϕ} → Term Γ (ϕ # μ ϕ) → Term Γ (μ ϕ)
    nfμ : ∀ {Γ ϕ} → (F : Term Γ (ϕ # μ ϕ)) → NF Γ (ϕ # μ ϕ) F → NF Γ (μ ϕ) (μ-intr F)

    --ν-intr : ∀ {Γ ρ} ϕ → AbsT Term Γ ρ (ϕ # ρ) → Term Γ ρ → Term Γ (ν ϕ)
    nfν : ∀ {Γ ρ} ϕ → (S : AbsT Term Γ ρ (ϕ # ρ)) → (X : Term Γ ρ) → NF ((π₁ S , ρ) ∷ Γ) (ϕ # ρ) (π₂ S) → NF Γ ρ X → NF Γ (ν ϕ) (ν-intr ϕ S X)
