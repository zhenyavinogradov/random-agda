module _ where

module _ where
  record ⊤ : Set where
    constructor tt

  infixr 5 _,_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  infixr 5 _,,_
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,,_
    field
      first : A
      second : B first

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}
    
  _€_ : {A B : Set} → A → (A → B) → B
  x € f = f x

  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

  transport : {A : Set} {a b : A} → (P : A → Set) → a ≡ b → P a → P b
  transport P refl Pa = Pa

  cong : {A B : Set} {a a' : A} → (f : A → B) → a ≡ a' → f a ≡ f a'
  cong f refl = refl

  infixr 15 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  single : ∀ {A} → A → List A
  single a = a ∷ ε

  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  data Has {A : Set} : List A → A → Set where
    here : ∀ {a as} → Has (a ∷ as) a
    there : ∀ {a b as} → Has as a → Has (b ∷ as) a

  $0 : ∀ {A a0 as} → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as} → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $0 = here
  $1 = there here
  $2 = there (there here)
  $3 = there (there (there here))

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  _++'_ : {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
  ε ++' Pys = Pys
  (Px ∷ Pxs) ++' Pys = Px ∷ (Pxs ++' Pys)

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get (x ∷ env) here = x
  get (x ∷ env) (there var) = get env var

  mapAll : {A : Set} {P Q : A → Set} {as : List A} → ({a : A} → P a → Q a) → All P as → All Q as
  mapAll f ε = ε
  mapAll f (Pa ∷ Pas) = f Pa ∷ mapAll f Pas

  data All2 {A : Set} {P : A → Set} (P2 : {a : A} → P a → Set) : {as : List A} → All P as → Set where
    ε : All2 P2 ε
    _∷_ : ∀ {a as Pa Pas} → P2 Pa → All2 P2 {as} Pas → All2 P2 {a ∷ as} (Pa ∷ Pas)

  _++2_ : ∀ {A P xs ys Pxs Pys} {P2 : {a : A} → P a → Set} → All2 P2 {xs} Pxs → All2 P2 {ys} Pys → All2 {A} {P} P2 {xs ++ ys} (Pxs ++' Pys)
  ε ++2 Pys = Pys
  (Px ∷ Pxs) ++2 Pys = Px ∷ (Pxs ++2 Pys)

  get2 : ∀ {A P a as Pas} → {P2 : {a : A} → P a → Set} → All2 {A} {P} P2 {as} Pas → (i : Has as a) → P2 (get Pas i)
  get2 (x ∷ x₁) here = x
  get2 (x ∷ x₁) (there i) = get2 x₁ i

  mapAll2 : {A : Set} {P : A → Set} {P2 Q2 : {a : A} → P a → Set} {as : List A} {Pas : All P as} → ({a : A} → {Pa : P a} → P2 Pa → Q2 Pa) → All2 P2 Pas → All2 Q2 Pas
  mapAll2 f ε = ε
  mapAll2 f (P2Pa ∷ P2Pas) = f P2Pa ∷ mapAll2 f P2Pas


data Type : Set where
  σ π : List Type → Type
  _⇒_ : List Type → Type → Type
  nat : Type
  -- list : Type → Type
  -- stream : Type → Type

Context : Set
Context = List Type

Var : Context → Type → Set
Var Γ τ = Has Γ τ

mutual
  data Expr (Γ : Context) : Type → Set where
    lambda : (ρs : List Type) (τ : Type) → Term (ρs ++ Γ) τ → Expr Γ (ρs ⇒ τ)
    call : (ρs : List Type) (τ : Type) → Var Γ (ρs ⇒ τ) → All (\ρ → Var Γ ρ) ρs → Expr Γ τ

    inj : (τs : List Type) (τ : Type) → Has τs τ → Var Γ τ → Expr Γ (σ τs)
    case : (τs : List Type) (ρ : Type) → Var Γ (σ τs) → All (\τ → Term (τ ∷ Γ) ρ) τs → Expr Γ ρ

    tuple : (τs : List Type) → All (\τ → Var Γ τ) τs → Expr Γ (π τs)
    untuple : (τs : List Type) (ρ : Type) → Var Γ (π τs) → Term (τs ++ Γ) ρ → Expr Γ ρ

    zero : Expr Γ nat
    succ : Var Γ nat → Expr Γ nat
    foldNat : (ρ : Type) → Var Γ nat → Term Γ ρ → Term (ρ ∷ Γ) ρ → Expr Γ ρ
  
  data Term : Context → Type → Set where
    ret : ∀ {Γ τ} → Var Γ τ → Term Γ τ 
    set : ∀ {Γ ρ τ} → Expr Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ

mutual
  data Value : Type → Set where
    #closure : ∀ {ρs τ} → Closure ρs τ → Value (ρs ⇒ τ)
    #tuple : ∀ {τs} → All Value τs → Value (π τs)
    #inj : ∀ {τs τ} → (i : Has τs τ) → Value τ → Value (σ τs)
    #zero : Value nat
    #succ : Value nat → Value nat
    -- #nat : ℕ → Value nat
    -- #list : List (Value τ) → Value (list τ)
    -- #conat : ∀ {ρ} → Value ρ → Closure ρ σ[π[],ρ] → Value conat
    -- #stream : ∀ {ρ} → Value ρ → Closure ρ π[τ,ρ] → Value (stream τ)

  Env : Context → Set
  Env Γ = All Value Γ
  
  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → Term (ρs ++ Γ) τ → Closure ρs τ

data Cont : List Type → Type → Set where
  ε : ∀ {ρ} → Cont (single ρ) ρ
  _∷_ : ∀ {ρs ϕ τ} → Closure ρs ϕ → Cont (single ϕ) τ → Cont ρs τ

applyFunction : ∀ {ρs τ} → Value (ρs ⇒ τ) → All Value ρs → Cont ε τ
applyFunction (#closure (envf & termf)) vs = (vs ++' envf) & termf ∷ ε

applyCase : ∀ {Γ τs ρ} → Env Γ → Value (σ τs) → All (\τ → Term (τ ∷ Γ) ρ) τs → Cont ε ρ
applyCase env (#inj i v) terms = ((v ∷ env) & get terms i) ∷ ε

applyTuple : ∀ {Γ τs ρ} → Env Γ → Value (π τs) → Term (τs ++ Γ) ρ → Cont ε ρ
applyTuple env (#tuple vs) term = ((vs ++' env) & term) ∷ ε

getContFoldNat : ∀ {ρ Γ} → Env Γ → Value nat → Term (ρ ∷ Γ) ρ → Cont (single ρ) ρ
getContFoldNat env #zero terms = ε
getContFoldNat env (#succ v) terms = (env & terms) ∷ getContFoldNat env v terms

applyFoldNat : ∀ {ρ Γ} → Env Γ → Value nat → Term Γ ρ → Term (ρ ∷ Γ) ρ → Cont ε ρ
applyFoldNat env n termz terms = (env & termz) ∷ getContFoldNat env n terms
  
stepExpr : ∀ {Γ τ} → Env Γ → Expr Γ τ → Value τ + Cont ε τ
stepExpr env (lambda ρs τ term) = inl (#closure (env & term))
stepExpr env (call ρs τ f xs) = inr (applyFunction (get env f) (mapAll (get env) xs))
stepExpr env (inj τs τ i x) = inl (#inj i (get env x))
stepExpr env (case τs ρ x terms) = inr (applyCase env (get env x) terms)
stepExpr env (tuple τs xs) = inl (#tuple (mapAll (get env) xs))
stepExpr env (untuple τs ρ x term) = inr (applyTuple env (get env x) term)
stepExpr env zero = inl #zero
stepExpr env (succ x) = inl (#succ (get env x))
stepExpr env (foldNat ρ x termz terms) = inr (applyFoldNat env (get env x) termz terms)

composeCont : ∀ {ρs τ ϕ} → Cont ρs τ → Cont (single τ) ϕ → Cont ρs ϕ
composeCont ε cont2 = cont2
composeCont (cl1 ∷ cont1) cont2 = cl1 ∷ composeCont cont1 cont2

applyEnvClosure : ∀ {τs ϕ} → Env τs → Closure τs ϕ → Closure ε ϕ
applyEnvClosure env (env' & term) = (env ++' env') & term

applyEnvCont : ∀ {τs ϕ} → Env τs → Cont τs ϕ → Value ϕ + Cont ε ϕ
applyEnvCont vs (cl ∷ cont) = inr (applyEnvClosure vs cl ∷ cont)
applyEnvCont (v ∷ ε) ε = inl v

applyVCont : ∀ {τ ϕ} → Value τ → Cont (single τ) ϕ → Value ϕ + Cont ε ϕ
applyVCont v cont = applyEnvCont (v ∷ ε)  cont

applyVSCont : ∀ {τ ϕ} → Value τ + Cont ε τ → Cont (single τ) ϕ → Value ϕ + Cont ε ϕ
applyVSCont (inl v) cont = applyVCont v cont
applyVSCont (inr cont') cont = inr (composeCont cont' cont)

stepExprCont : ∀ {Γ τ ϕ} → Env Γ → Expr Γ τ → Cont (single τ) ϕ → Value ϕ + Cont ε ϕ
stepExprCont env expr cont = applyVSCont (stepExpr env expr) cont

stepTermCont : ∀ {Γ τ ϕ} → Env Γ → Term Γ τ → Cont (single τ) ϕ → Value ϕ + Cont ε ϕ
stepTermCont env (ret x) cont = applyVCont (get env x) cont
stepTermCont env (set expr term) cont = stepExprCont env expr ((env & term) ∷ cont)

step : ∀ {ϕ} → Cont ε ϕ → Value ϕ + Cont ε ϕ
step ((env & term) ∷ cont) = stepTermCont env term cont


VS : Type → Set
VS τ = Value τ + Cont ε τ

mutual
  {-# NO_POSITIVITY_CHECK #-} -- inductive on τ
  data Finishes {τ} : VS τ → Set where
    fin : ∀ {v} → NormValue {τ} v → Finishes (inl v)
    nex : ∀ {s} → Finishes (step s) → Finishes (inr s)

  NormValue : ∀ {τ} → Value τ → Set
  NormValue {ρs ⇒ τ} (#closure cl) = GoodClosure {ρs} {τ} cl
  NormValue {σ τs} (#inj i v) = NormGet i v
  NormValue {π τs} (#tuple vs) = NormEnv {τs} vs
  NormValue {nat} _ = ⊤

  GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set
  GoodClosure {ρs} {τ} closure = ∀ {values} → NormEnv {ρs} values → Finishes {τ} (inr (applyEnvClosure values closure ∷ ε))

  NormGet : ∀ {τs τ} → Has τs τ → Value τ → Set
  NormGet {τ ∷ τs} here v = NormValue {τ} v
  NormGet {τ ∷ τs} (there i) v = NormGet {τs} i v

  NormEnv : ∀ {τs} → Env τs → Set
  NormEnv ε = ⊤
  NormEnv (value ∷ env) = NormValue value × NormEnv env

mutual
  data Finishes0 {τ} : VS τ → Set where
    fin : ∀ {v} → NormValue' {τ} v → Finishes0 (inl v)
    nex : ∀ {s} → Finishes0 (step s) → Finishes0 (inr s)

  Finishes' : ∀ {τ} → VS τ → Set
  Finishes' = Finishes0

  NormValue' : ∀ {τ} → Value τ → Set
  NormValue' {ρs ⇒ τ} (#closure cl) = GoodClosure' {ρs} {τ} cl
  NormValue' {σ τs} (#inj i v) = NormGet' i v
  NormValue' {π τs} (#tuple vs) = NormEnv' {τs} vs
  NormValue' {nat} _ = ⊤

  GoodClosure' : ∀ {ρs τ} → Closure ρs τ → Set
  GoodClosure' {ρs} {τ} closure = ∀ {values} → NormEnv' {ρs} values → Finishes' {τ} (inr (applyEnvClosure values closure ∷ ε))

  NormGet' : ∀ {τs τ} → Has τs τ → Value τ → Set
  NormGet' {τ ∷ τs} here v = NormValue' {τ} v
  NormGet' {τ ∷ τs} (there i) v = NormGet' {τs} i v

  NormEnv' : ∀ {τs} → Env τs → Set
  NormEnv' ε = ⊤
  NormEnv' (value ∷ env) = NormValue' value × NormEnv' env

GoodTerm : ∀ {Γ τ} → Term Γ τ → Set
GoodTerm {Γ} {τ} term = ∀ {env} → NormEnv {Γ} env → Finishes (inr ((env & term) ∷ ε))

data NormClosure {ρs τ} : Closure ρs τ → Set where
  _&_ : ∀ {Γ env term} → NormEnv {Γ} env → GoodTerm term → NormClosure (env & term)

GoodVS : ∀ {τ} → VS τ → Set
GoodVS vs = Finishes vs

GoodCont : ∀ {ρs τ} → Cont ρs τ → Set
GoodCont cont = ∀ {vs} → NormEnv vs → Finishes (applyEnvCont vs cont)

data NormExpr {Γ} : ∀ {τ} → Expr Γ τ → Set where
  normLambda : ∀ {ρs τ term} → GoodTerm term → NormExpr (lambda ρs τ term)
  normCall : ∀ {ρs τ} f xs → NormExpr (call ρs τ f xs)
  normInj : ∀ {τs τ i} x → NormExpr (inj τs τ i x)
  normCase : ∀ {τs ρ} x {terms} → All2 GoodTerm terms → NormExpr (case τs ρ x terms)
  normTuple : ∀ {τs} xs → NormExpr (tuple τs xs)
  normUntuple : ∀ {τs ρ} x {term} → GoodTerm term → NormExpr (untuple τs ρ x term)
  normZero : NormExpr zero
  normSucc : ∀ x → NormExpr (succ x)
  normFoldNat : ∀ {ρ} x {termz terms} → GoodTerm termz → GoodTerm terms → NormExpr (foldNat ρ x termz terms)

data NormCont : ∀ {ρs τ} → Cont ρs τ → Set where
  ε : ∀ {τ} → NormCont {single τ} {τ} ε
  -- _∷_ : ∀ {ρs ϕ τ cl cont} → NormClosure {ρs} {ϕ} cl → NormCont {single ϕ} {τ} cont → NormCont (cl ∷ cont)
  _∷_ : ∀ {ρs ϕ τ cl cont} → GoodClosure {ρs} {ϕ} cl → NormCont {single ϕ} {τ} cont → NormCont (cl ∷ cont)

data NormVS {τ} : VS τ → Set where
  normInl : ∀ {v} → NormValue v → NormVS (inl v)
  normInr : ∀ {c} → NormCont c → NormVS (inr c)

composeApplyEnvContIsCompose : ∀ {τs ϕ ϕ'} → (env : Env τs) → (cont1 : Cont τs ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (applyEnvCont env cont1) cont2 ≡ applyEnvCont env (composeCont cont1 cont2)
composeApplyEnvContIsCompose env (cl ∷ cont1) cont2 = refl
composeApplyEnvContIsCompose (v ∷ ε) ε cont2 = refl

composeContIsCompose : ∀ {ρs τ ϕ ϕ'} → (cont0 : Cont ρs τ) → (cont1 : Cont (single τ) ϕ) → (cont2 : Cont (single ϕ) ϕ') → composeCont (composeCont cont0 cont1) cont2 ≡ composeCont cont0 (composeCont cont1 cont2)
composeContIsCompose ε cont1 cont2 = refl
composeContIsCompose (closure ∷ cont0) cont1 cont2 = cong (\x → closure ∷ x) (composeContIsCompose cont0 cont1 cont2)

composeApplyVSContIsCompose : ∀ {τ ϕ ϕ'} → (vs : VS τ) → (cont1 : Cont (single τ) ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (applyVSCont vs cont1) cont2 ≡ applyVSCont vs (composeCont cont1 cont2)
composeApplyVSContIsCompose (inl value) cont1 cont2 = composeApplyEnvContIsCompose (value ∷ ε) cont1 cont2
composeApplyVSContIsCompose (inr cont') cont1 cont2 = cong inr (composeContIsCompose cont' cont1 cont2)

composeStepExprContIsCompose : ∀ {Γ τ ϕ ϕ'} → (env : Env Γ) → (expr : Expr Γ τ) → (cont1 : Cont (single τ) ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (stepExprCont env expr cont1) cont2 ≡ stepExprCont env expr (composeCont cont1 cont2)
composeStepExprContIsCompose env expr cont1 cont2 = composeApplyVSContIsCompose (stepExpr env expr) cont1 cont2

composeStepTermContIsCompose : ∀ {ρs τ ϕ ϕ'} → (env : Env ρs) → (term : Term ρs τ) → (cont1 : Cont (single τ) ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (stepTermCont env term cont1) cont2 ≡ stepTermCont env term (composeCont cont1 cont2)
composeStepTermContIsCompose env (ret x) ε cont2 = refl
composeStepTermContIsCompose env (ret x) (x₁ ∷ cont1) cont2 = refl
composeStepTermContIsCompose env (set expr term) cont1 cont2 = composeStepExprContIsCompose env expr ((env & term) ∷ cont1) cont2

composeStepIsStepCompose : ∀ {τ ϕ} → (cont1 : Cont ε τ) → (cont2 : Cont (single τ) ϕ) → applyVSCont (step cont1) cont2 ≡ step (composeCont cont1 cont2)
composeStepIsStepCompose ((env & term) ∷ cont1) cont2 = composeStepTermContIsCompose env term cont1 cont2

goodGoodApplyVSCont : ∀ {τ ϕ vs cont} → GoodVS {τ} vs → GoodCont {single τ} {ϕ} cont → GoodVS (applyVSCont vs cont)
--goodGoodApplyVSCont {vs = inl value} (fin norm-value) good-cont = good-cont (norm-value ∷ ε)
goodGoodApplyVSCont {vs = inl value} (fin norm-value) good-cont = good-cont {!!}
goodGoodApplyVSCont {vs = inr cont1} {cont = cont2} (nex good-vs) good-cont2 = nex (transport Finishes (composeStepIsStepCompose cont1 cont2) (goodGoodApplyVSCont good-vs good-cont2))

goodNormCont : ∀ {ρs τ cont} → NormCont {ρs} {τ} cont → GoodCont {ρs} {τ} cont
-- goodNormCont {cont = (env & term) ∷ cont} ((norm-env & good-term) ∷ norm-cont) {values} norm-values = goodGoodApplyVSCont good-vs good-cont
goodNormCont {cont = (env & term) ∷ cont} (good-closure ∷ norm-cont) {values} norm-values = goodGoodApplyVSCont good-vs good-cont
  where
    good-vs : GoodVS (inr (((values ++' env) & term) ∷ ε))
    -- good-vs = good-term (norm-values ++2 norm-env)
    --good-vs = good-closure norm-values
    good-vs = {!!}

    good-cont1 : GoodCont ((env & term) ∷ ε)
    -- good-cont1 norm-vs = good-term (norm-vs ++2 norm-env) 
    --good-cont1 norm-vs = good-closure norm-vs
    good-cont1 norm-vs = {!!}

    good-cont : GoodCont cont
    good-cont = goodNormCont norm-cont
--goodNormCont ε (norm-value ∷ ε) = fin norm-value
goodNormCont ε _ = {!!}

goodNormVS : ∀ {τ vs} → NormVS {τ} vs → GoodVS vs
goodNormVS (normInl norm-value) = fin norm-value
-- goodNormVS (normInr norm-cont@((_ & _) ∷ _)) = goodNormCont norm-cont ε
--goodNormVS (normInr norm-cont@(_∷_ {cl = _ & _} _ _)) = goodNormCont norm-cont ε
goodNormVS (normInr norm-cont@(_∷_ {cl = _ & _} _ _)) = goodNormCont norm-cont {!!}

--goodTermMakesGoodClosure : ∀ {Γ ρs τ} env term → NormEnv {Γ} env → GoodTerm {ρs ++ Γ} {τ} term → 
goodNormClosure : ∀ {ρs τ closure} → NormClosure {ρs} {τ} closure → GoodClosure closure
--goodNormClosure (norm-env & good-term) norm-values = good-term (norm-values ++2 norm-env)
goodNormClosure (norm-env & good-term) = {!!}

normMapGet : ∀ {Γ τs env} → NormEnv {Γ} env → (xs : All (Var Γ) τs) → NormEnv {τs} (mapAll (get env) xs)
--normMapGet norm-env ε = ε
normMapGet norm-env ε = {!!}
--normMapGet norm-env (x ∷ xs) = get2 norm-env x ∷ normMapGet norm-env xs
normMapGet norm-env (x ∷ xs) = {!!}

normApplyFunction : ∀ {ρs τ vf vs} → NormValue {ρs ⇒ τ} vf → All2 NormValue vs → NormCont (applyFunction vf vs)
-- normApplyFunction {vf = #closure (envf & termf)} (norm-envf & good-termf) norm-vs = ((norm-vs ++2 norm-envf) & good-termf) ∷ ε
normApplyFunction {vf = #closure (envf & termf)} {vs} good-closure norm-vs = good-closure' ∷ ε
  where
    good-closure' : GoodClosure ((vs ++' envf) & termf)
    --good-closure' ε = good-closure norm-vs
    good-closure' = {!!}

normApplyCase : ∀ {Γ τs ρ env v terms} → NormEnv {Γ} env → NormValue {σ τs} v → All2 (GoodTerm {_ ∷ Γ} {ρ}) terms → NormCont (applyCase env v terms)
--normApplyCase {v = #inj i v} norm-env norm-v good-terms = ((norm-v ∷ norm-env) & (get2 good-terms i)) ∷ ε
--normApplyCase {v = #inj i v} norm-env norm-v good-terms = goodNormClosure ((norm-v ∷ norm-env) & get2 good-terms i) ∷ ε
normApplyCase {v = #inj i v} norm-env norm-v good-terms = goodNormClosure ({!!} & get2 good-terms i) ∷ ε

normApplyTuple : ∀ {Γ τs ρ env v term} → NormEnv {Γ} env → NormValue {π τs} v → GoodTerm {τs ++ Γ} {ρ} term → NormCont (applyTuple env v term)
--normApplyTuple {v = #tuple vs} norm-env norm-vs good-term = ((norm-vs ++2 norm-env) & good-term) ∷ ε
--normApplyTuple {v = #tuple vs} norm-env norm-vs good-term = goodNormClosure ((norm-vs ++2 norm-env) & good-term) ∷ ε
normApplyTuple {v = #tuple vs} norm-env norm-vs good-term = goodNormClosure ({!!} & good-term) ∷ ε

normGetContFoldNat : ∀ {ρ Γ env v term} → NormEnv {Γ} env → NormValue {nat} v → GoodTerm {ρ ∷ Γ} {ρ} term → NormCont (getContFoldNat env v term)
normGetContFoldNat {v = #zero} norm-env norm-value good-term = ε
--normGetContFoldNat {v = #succ v} norm-env norm-value good-term = (norm-env & good-term) ∷ normGetContFoldNat norm-env norm-value good-term
--normGetContFoldNat {v = #succ v} norm-env norm-value good-term = goodNormClosure (norm-env & good-term) ∷ normGetContFoldNat norm-env norm-value good-term
normGetContFoldNat {v = #succ v} norm-env norm-value good-term = goodNormClosure (norm-env & good-term) ∷ normGetContFoldNat norm-env {!!} good-term

normApplyFoldNat : ∀ {ρ Γ env v termZ termS} → NormEnv {Γ} env → NormValue {nat} v → GoodTerm {Γ} {ρ} termZ → GoodTerm {ρ ∷ Γ} {ρ} termS → NormCont (applyFoldNat env v termZ termS)
--normApplyFoldNat norm-env norm-value good-termZ good-termS = (norm-env & good-termZ) ∷ normGetContFoldNat norm-env norm-value good-termS
normApplyFoldNat norm-env norm-value good-termZ good-termS = goodNormClosure (norm-env & good-termZ) ∷ normGetContFoldNat norm-env norm-value good-termS

normStepExpr : ∀ {Γ τ expr env} → NormEnv {Γ} env → NormExpr {Γ} {τ} expr → NormVS (stepExpr env expr)
--normStepExpr norm-env (normLambda good-term) = normInl (norm-env & good-term)
normStepExpr norm-env _ = {!!}
--normStepExpr norm-env (normLambda good-term) = normInl \norm-values → good-term (norm-values ++2 norm-env)
--normStepExpr norm-env (normCall f xs) = normInr (normApplyFunction (get2 norm-env f) (normMapGet norm-env xs))
--normStepExpr norm-env (normInj x) = normInl (get2 norm-env x)
--normStepExpr norm-env (normCase x good-terms) = normInr (normApplyCase norm-env (get2 norm-env x) good-terms)
--normStepExpr norm-env (normTuple xs) = normInl (normMapGet norm-env xs)
--normStepExpr norm-env (normUntuple x good-term) = normInr (normApplyTuple norm-env (get2 norm-env x) good-term)
--normStepExpr norm-env normZero = normInl tt
--normStepExpr norm-env (normSucc x) = normInl (get2 norm-env x)
--normStepExpr norm-env (normFoldNat x good-termz good-terms) = normInr (normApplyFoldNat norm-env (get2 norm-env x) good-termz good-terms)

normComposeCont : ∀ {ρs τ ϕ cont1 cont2} → NormCont {ρs} {τ} cont1 → NormCont {single τ} {ϕ} cont2 → NormCont (composeCont cont1 cont2)
normComposeCont ε norm-cont2 = norm-cont2
normComposeCont (norm-closure ∷ norm-cont1) norm-cont2 = norm-closure ∷ normComposeCont norm-cont1 norm-cont2

normApplyVSCont : ∀ {τ ϕ vs cont} → NormVS {τ} vs → NormCont {single τ} {ϕ} cont → NormVS (applyVSCont vs cont)
normApplyVSCont (normInl norm-value) ε = normInl norm-value
--normApplyVSCont (normInl norm-value) ((norm-env & good-term) ∷ norm-cont) = normInr (((norm-value ∷ norm-env) & good-term) ∷ norm-cont)
normApplyVSCont {cont = closure@(_ & _) ∷ _} (normInl {value} norm-value) (good-closure ∷ norm-cont) = normInr (good-closure' ∷ norm-cont)
  where
    good-closure' : GoodClosure (applyEnvClosure (value ∷ ε) closure)
    --good-closure' ε = good-closure (norm-value ∷ ε)
    good-closure' = {!!}
normApplyVSCont (normInr norm-cont') norm-cont = normInr (normComposeCont norm-cont' norm-cont)

goodApplyVSCont : ∀ {τ ϕ vs cont} → NormVS {τ} vs → NormCont {single τ} {ϕ} cont → GoodVS (applyVSCont vs cont)
goodApplyVSCont norm-vs norm-cont = goodNormVS (normApplyVSCont norm-vs norm-cont)

goodStepExprCont : ∀ {Γ τ ρ expr env cont} → NormEnv {Γ} env → NormExpr {Γ} {τ} expr → NormCont {single τ} {ρ} cont → GoodVS (stepExprCont env expr cont)
goodStepExprCont norm-env norm-expr norm-cont = goodApplyVSCont (normStepExpr norm-env norm-expr) norm-cont

mutual
  normExpr : ∀ {Γ τ} → (expr : Expr Γ τ) → NormExpr expr
  normExpr (lambda ρs τ term) = normLambda (goodTerm term)
  normExpr (call ρs τ f xs) = normCall f xs
  normExpr (inj τs τ i x) = normInj x
  normExpr (case τs ρ x terms) = normCase x (goodAllTerms terms)
  normExpr (tuple τs x) = normTuple x
  normExpr (untuple τs ρ xs term) = normUntuple xs (goodTerm term)
  normExpr zero = normZero
  normExpr (succ x) = normSucc x
  normExpr (foldNat ρ x termZ termS) = normFoldNat x (goodTerm termZ) (goodTerm termS)

  goodAllTerms : ∀ {Γ τs ρ} → (terms : All (\τ → Term (τ ∷ Γ) ρ) τs) → All2 GoodTerm terms
  goodAllTerms ε = ε
  goodAllTerms (term ∷ terms) = goodTerm term ∷ goodAllTerms terms

  goodTerm : ∀ {Γ τ} → (term : Term Γ τ) → GoodTerm term
  --goodTerm (ret x) norm-env = nex (fin (get2 norm-env x))
  goodTerm (ret x) norm-env = nex (fin {!!})
  --goodTerm (set expr term) norm-env = nex (goodStepExprCont norm-env (normExpr expr) ((norm-env & goodTerm term) ∷ ε))
  goodTerm (set expr term) {env} norm-env = nex (goodStepExprCont norm-env (normExpr expr) (good-closure ∷ ε))
    where
      good-term : GoodTerm term
      good-term = goodTerm term

      good-closure : GoodClosure (env & term)
      --good-closure norm-values = good-term (norm-values ++2 norm-env)
      good-closure = {!!}

result : ∀ {τ vc} → Finishes {τ} vc → Value τ
result (fin {v} _norm) = v
result (nex c) = result c

eval : ∀ {τ} → Term ε τ → Value τ
--eval term = result (goodTerm term ε)
eval term = result (goodTerm term {!!})

module Test where
  infixr 5 _▸_
  _▸_ : ∀ {Γ ρ τ} → Expr Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ
  _▸_ = set

  num : ∀ Γ → ℕ → Term Γ nat
  num Γ n = set zero (go n) where
    go : {Γ : Context} → ℕ → Term (nat ∷ Γ) nat
    go zero = ret here
    go (succ n) = succ here ▸ go n
  
  add : ∀ Γ → Term (nat ∷ nat ∷ Γ) nat
  add _ =
    foldNat nat $1
        (ret $0)
        ( succ $0 ▸
          ret $0
        )
    ▸ ret here
  
  stepn : {τ : Type} → ℕ → Cont ε τ → Value τ + Cont ε τ
  stepn zero s = inr s
  stepn (succ n) s with step s
  … | inl v = inl v
  … | inr s' = stepn n s'
  
  run : ∀ {τ} → ℕ → Term ε τ → Value τ + Cont ε τ
  run i term = stepn i ((ε & term) ∷ ε)
  
  test : Term ε nat
  test =
    lambda _ _ (num _ 2) ▸
    call _ _ $0 ε ▸
    lambda _ _ (num _ 3) ▸
    call _ _ $0 ε ▸
    lambda (nat ∷ nat ∷ ε) _ (add _) ▸
    call _ _ $0 ($1 ∷ $3 ∷ ε) ▸
    ret $0

  _ : Set
  _ = {!eval test!}

module Extra where
  mutual
    normValue : ∀ {τ} → (value : Value τ) → NormValue value
    --normValue (#closure (env & term)) = normEnv env & goodTerm term
    normValue _ = {!!}
    --normValue (#closure closure) = goodClosure closure
    --normValue (#tuple values) = normAllValues values
    --normValue (#inj i value) = normValue value
    --normValue #zero = tt
    --normValue (#succ value) = normValue value
  
    normAllValues : ∀ {τs} → (values : All Value τs) → All2 NormValue values
    normAllValues ε = ε
    normAllValues (value ∷ values) = normValue value ∷ normAllValues values
    
    normEnv : ∀ {Γ} → (env : Env Γ) → NormEnv env
    normEnv = {!!}
    --normEnv ε = ε
    --normEnv (value ∷ env) = normValue value ∷ normEnv env

    goodClosure : ∀ {ρs τ} → (closure : Closure ρs τ) → GoodClosure closure
    --goodClosure (env & term) norm-values = goodTerm term (norm-values ++2 normEnv env)
    goodClosure (env & term) = {!!}
  
  apply : ∀ {Γ τ} → Term Γ τ → Env Γ → Value τ
  apply term env = result (goodTerm term (normEnv env)) 
