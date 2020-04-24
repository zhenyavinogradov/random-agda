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

Var : List Type → Type → Set
Var Γ τ = Has Γ τ

mutual
  data Expr (Γ : List Type) : Type → Set where
    lambda : (ρs : List Type) (τ : Type) → Term (ρs ++ Γ) τ → Expr Γ (ρs ⇒ τ)
    call : (ρs : List Type) (τ : Type) → Var Γ (ρs ⇒ τ) → All (\ρ → Var Γ ρ) ρs → Expr Γ τ

    inj : (τs : List Type) (τ : Type) → Has τs τ → Var Γ τ → Expr Γ (σ τs)
    case : (τs : List Type) (ρ : Type) → Var Γ (σ τs) → All (\τ → Term (τ ∷ Γ) ρ) τs → Expr Γ ρ

    tuple : (τs : List Type) → All (\τ → Var Γ τ) τs → Expr Γ (π τs)
    untuple : (τs : List Type) (ρ : Type) → Var Γ (π τs) → Term (τs ++ Γ) ρ → Expr Γ ρ

    zero : Expr Γ nat
    succ : Var Γ nat → Expr Γ nat
    foldNat : (ρ : Type) → Var Γ nat → Term Γ ρ → Term (ρ ∷ Γ) ρ → Expr Γ ρ
  
  data Term (Γ : List Type) : Type → Set where
    ret : ∀ {τ} → Var Γ τ → Term Γ τ 
    set : ∀ {ρ τ} → Expr Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ

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

  Env : List Type → Set
  Env Γ = All Value Γ
  
  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → Term (ρs ++ Γ) τ → Closure ρs τ

data Cont : List Type → Type → Set where
  ε : ∀ {ρ} → Cont (single ρ) ρ
  _∷_ : ∀ {ρs ϕ τ} → Closure ρs ϕ → Cont (single ϕ) τ → Cont ρs τ

VS : Type → Set
VS τ = Value τ + Cont ε τ

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
applyVCont v cont = applyEnvCont (v ∷ ε) cont

applyVSCont : ∀ {τ ϕ} → Value τ + Cont ε τ → Cont (single τ) ϕ → Value ϕ + Cont ε ϕ
applyVSCont (inl v) cont = applyVCont v cont
applyVSCont (inr cont') cont = inr (composeCont cont' cont)

step : ∀ {ϕ} → Cont ε ϕ → Value ϕ + Cont ε ϕ
step ((env & ret x) ∷ cont) = applyVCont (get env x) cont
step ((env & set expr term) ∷ cont) = applyVSCont (stepExpr env expr) ((env & term) ∷ cont)

composeApplyEnvContIsCompose : ∀ {τs ϕ ϕ'} → (env : Env τs) → (cont1 : Cont τs ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (applyEnvCont env cont1) cont2 ≡ applyEnvCont env (composeCont cont1 cont2)
composeApplyEnvContIsCompose env (cl ∷ cont1) cont2 = refl
composeApplyEnvContIsCompose (v ∷ ε) ε cont2 = refl

composeContIsCompose : ∀ {ρs τ ϕ ϕ'} → (cont0 : Cont ρs τ) → (cont1 : Cont (single τ) ϕ) → (cont2 : Cont (single ϕ) ϕ') → composeCont (composeCont cont0 cont1) cont2 ≡ composeCont cont0 (composeCont cont1 cont2)
composeContIsCompose ε cont1 cont2 = refl
composeContIsCompose (closure ∷ cont0) cont1 cont2 = cong (\x → closure ∷ x) (composeContIsCompose cont0 cont1 cont2)

composeApplyVSContIsCompose : ∀ {τ ϕ ϕ'} → (vs : VS τ) → (cont1 : Cont (single τ) ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (applyVSCont vs cont1) cont2 ≡ applyVSCont vs (composeCont cont1 cont2)
composeApplyVSContIsCompose (inl value) cont1 cont2 = composeApplyEnvContIsCompose (value ∷ ε) cont1 cont2
composeApplyVSContIsCompose (inr cont') cont1 cont2 = cong inr (composeContIsCompose cont' cont1 cont2)

composeStepIsStepCompose : ∀ {τ ϕ} → (cont1 : Cont ε τ) → (cont2 : Cont (single τ) ϕ) → applyVSCont (step cont1) cont2 ≡ step (composeCont cont1 cont2)
composeStepIsStepCompose ((env & ret x) ∷ cont1) cont2 = composeApplyEnvContIsCompose (get env x ∷ ε) cont1 cont2
composeStepIsStepCompose ((env & set expr term) ∷ cont1) cont2 = composeApplyVSContIsCompose (stepExpr env expr) ((env & term) ∷ cont1) cont2

record PredVS (τ : Type) : Set₁ where
  constructor mkPredVS
  field
    applyPredVS : VS τ → Set
    applyPredV : Value τ → Set
open PredVS public

data All₁ {A : Set} (P : A → Set₁) : List A → Set₁ where
  ε : All₁ P ε
  _∷_ : ∀ {a as} → P a → All₁ P as → All₁ P (a ∷ as)

data All2₁ {A : Set} {P : A → Set} (P2 : {a : A} → P a → Set₁) : {as : List A} → All P as → Set₁ where
  ε : All2₁ P2 ε
  _∷_ : ∀ {a as Pa Pas} → P2 Pa → All2₁ P2 {as} Pas → All2₁ P2 {a ∷ as} (Pa ∷ Pas)

get₁ : ∀ {A P a as} → All₁ {A} P as → Has as a → P a
get₁ (x ∷ env) here = x
get₁ (x ∷ env) (there var) = get₁ env var


AllPredVS : List Type → Set₁
AllPredVS τs = All₁ PredVS τs

AllPredVS' : List Type → Set₁
AllPredVS' τs = (τ : Type) → Has τs τ → PredVS τ

getAllPredVS : ∀ {τs τ} → AllPredVS τs → Has τs τ → Value τ → Set
getAllPredVS (Fin-τ ∷ Fin-τs) here value = applyPredV Fin-τ value
getAllPredVS (Fin-τ ∷ Fin-τs) (there i) value = getAllPredVS Fin-τs i value

NormValueF : ∀ {τ} → PredVS τ → Value τ → Set
NormValueF Fin-τ value = applyPredV Fin-τ value

NormEnvF : ∀ {τs} → AllPredVS τs → Env τs → Set
NormEnvF ε ε = ⊤
NormEnvF (Fin-τ ∷ Fin-τs) (value ∷ values) = NormValueF Fin-τ value × NormEnvF Fin-τs values

GoodClosureF : ∀ {ρs τ} → AllPredVS ρs → PredVS τ → Closure ρs τ → Set
GoodClosureF {ρs} {τ} Fin-ρs Fin-τ closure = ∀ {values} → NormEnvF {ρs} Fin-ρs values → applyPredVS Fin-τ (inr (applyEnvClosure values closure ∷ ε))

NormValue-⇒F : ∀ {ρs τ} → (Fin-ρs : AllPredVS ρs) (Fin-τ : PredVS τ) → Value (ρs ⇒ τ) → Set
NormValue-⇒F Fin-ρs Fin-τ (#closure cl) = GoodClosureF Fin-ρs Fin-τ cl

NormValue-πF : ∀ {τs} → (Fin-τs : AllPredVS τs) → Value (π τs) → Set
NormValue-πF Fin-τs (#tuple vs) = NormEnvF Fin-τs vs

--NormValue-σF : ∀ {τs} → (Fin-τs : AllPredVS τs) → Value (σ τs) → Set
--NormValue-σF Fin-τs (#inj i v) = getAllPredVS Fin-τs i v
data NormValue-σF {τs} (Fin-τs : AllPredVS τs) : Value (σ τs) → Set where
  normInj : ∀ {τ} → (i : Has τs τ) → {v : Value τ} → applyPredV (get₁ Fin-τs i) v → NormValue-σF Fin-τs (#inj i v)

NormValue-natF : Value nat → Set
NormValue-natF value = ⊤

data GoodVSF {τ} (Norm-τ : Value τ → Set) : VS τ → Set where
  fin : ∀ {v} → Norm-τ v → GoodVSF Norm-τ (inl v)
  nex : ∀ {s} → GoodVSF Norm-τ (step s) → GoodVSF Norm-τ (inr s)

mutual
  GoodVSPred : (τ : Type) → PredVS τ
  GoodVSPred τ = mkPredVS (GoodVSF (NormValue' τ)) (NormValue' τ)

  NormValue' : (τ : Type) → Value τ → Set
  NormValue' (ρs ⇒ τ) = NormValue-⇒F (AllGoodVSPred ρs) (GoodVSPred τ)
  NormValue' (σ τs) = NormValue-σF (AllGoodVSPred τs)
  NormValue' (π τs) = NormValue-πF (AllGoodVSPred τs)
  NormValue' nat = NormValue-natF
  
  AllGoodVSPred : (τs : List Type) → AllPredVS τs
  AllGoodVSPred ε = ε
  AllGoodVSPred (τ ∷ τs) = GoodVSPred τ ∷ AllGoodVSPred τs

GoodVS : ∀ {τ} → VS τ → Set
GoodVS {τ} = applyPredVS (GoodVSPred τ)

GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set
GoodClosure {ρs} {τ} = GoodClosureF (AllGoodVSPred ρs) (GoodVSPred τ)

NormValue : ∀ {τ} → Value τ → Set
NormValue {τ} = NormValue' τ

NormEnv : ∀ {τs} → Env τs → Set
NormEnv {τs} = NormEnvF (AllGoodVSPred τs)

GoodTerm : ∀ {Γ τ} → Term Γ τ → Set
GoodTerm {Γ} {τ} term = ∀ {env} → NormEnv {Γ} env → GoodVS (inr ((env & term) ∷ ε))

data NormClosure {ρs τ} : Closure ρs τ → Set where
  _&_ : ∀ {Γ env term} → NormEnv {Γ} env → GoodTerm term → NormClosure (env & term)

GoodCont : ∀ {ρs τ} → Cont ρs τ → Set
GoodCont cont = ∀ {vs} → NormEnv vs → GoodVS (applyEnvCont vs cont)

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
  _∷_ : ∀ {ρs ϕ τ cl cont} → GoodClosure {ρs} {ϕ} cl → NormCont {single ϕ} {τ} cont → NormCont (cl ∷ cont)

data NormVS {τ} : VS τ → Set where
  normInl : ∀ {v} → NormValue v → NormVS (inl v)
  normInr : ∀ {c} → NormCont c → NormVS (inr c)

goodGoodApplyVSCont : ∀ {τ ϕ vs cont} → GoodVS {τ} vs → GoodCont {single τ} {ϕ} cont → GoodVS (applyVSCont vs cont)
goodGoodApplyVSCont {vs = inl value} (fin norm-value) good-cont = good-cont (norm-value , tt)
goodGoodApplyVSCont {vs = inr cont1} {cont = cont2} (nex good-vs) good-cont2 = nex (transport GoodVS (composeStepIsStepCompose cont1 cont2) (goodGoodApplyVSCont good-vs good-cont2))

goodNormCont : ∀ {ρs τ cont} → NormCont {ρs} {τ} cont → GoodCont {ρs} {τ} cont
goodNormCont {cont = (env & term) ∷ cont} (good-closure ∷ norm-cont) {values} norm-values = goodGoodApplyVSCont {cont = cont} good-vs good-cont
  where
    good-vs : GoodVS (inr (((values ++' env) & term) ∷ ε))
    good-vs = good-closure norm-values

    good-cont1 : GoodCont ((env & term) ∷ ε)
    good-cont1 norm-vs = good-closure norm-vs

    good-cont : GoodCont cont
    good-cont = goodNormCont norm-cont
goodNormCont ε {v ∷ ε} (norm-value , tt) = fin norm-value

goodNormVS : ∀ {τ vs} → NormVS {τ} vs → GoodVS vs
goodNormVS (normInl norm-value) = fin norm-value
goodNormVS (normInr norm-cont@(_∷_ {cl = _ & _} _ _)) = goodNormCont norm-cont tt

appendNormEnv : ∀ {ρs τs values1 values2} → NormEnv {ρs} values1 → NormEnv {τs} values2 → NormEnv {ρs ++ τs} (values1 ++' values2)
appendNormEnv {values1 = ε} norm-values1 norm-values2 = norm-values2
appendNormEnv {values1 = value ∷ values1} (norm-value , norm-values1) norm-values2 = norm-value , appendNormEnv norm-values1 norm-values2

getNormEnv : ∀ {τs τ env} → NormEnv {τs} env → (x : Var τs τ) → NormValue (get env x)
getNormEnv {env = v ∷ env} (norm-v , norm-env) here = norm-v
getNormEnv {env = v ∷ env} (norm-v , norm-env) (there x) = getNormEnv norm-env x

goodNormClosure : ∀ {ρs τ closure} → NormClosure {ρs} {τ} closure → GoodClosure closure
goodNormClosure (norm-env & good-term) norm-values = good-term (appendNormEnv norm-values norm-env)

normMapGet : ∀ {Γ τs env} → NormEnv {Γ} env → (xs : All (Var Γ) τs) → NormEnv {τs} (mapAll (get env) xs)
normMapGet norm-env ε = tt
normMapGet norm-env (x ∷ xs) = getNormEnv norm-env x , normMapGet norm-env xs

normApplyFunction : ∀ {ρs τ vf vs} → NormValue {ρs ⇒ τ} vf → NormEnv vs → NormCont (applyFunction vf vs)
normApplyFunction {vf = #closure (envf & termf)} {vs} good-closure norm-vs = good-closure' ∷ ε
  where
    good-closure' : GoodClosure ((vs ++' envf) & termf)
    good-closure' {ε} norm-ε = good-closure norm-vs

lem : ∀ {τ} τs (i : Has τs τ) (v : Value τ) → applyPredV (get₁ (AllGoodVSPred τs) i) v → applyPredV (GoodVSPred τ) v
lem τs here v norm-v = norm-v
lem (τ ∷ τs) (there i) v = lem τs i v

lem' : ∀ {τ} τs (i : Has τs τ) (v : Value τ) → applyPredV (GoodVSPred τ) v → applyPredV (get₁ (AllGoodVSPred τs) i) v
lem' τs here v norm-v = norm-v
lem' (τ ∷ τs) (there i) v = lem' τs i v

normApplyCase : ∀ {Γ τs ρ env v terms} → NormEnv {Γ} env → NormValue {σ τs} v → All2 (GoodTerm {_ ∷ Γ} {ρ}) terms → NormCont (applyCase env v terms)
normApplyCase {v = #inj {τs} {τ} i v} norm-env (normInj _ norm-v) good-terms = goodNormClosure ((lem τs i v norm-v , norm-env) & get2 good-terms i) ∷ ε


normApplyTuple : ∀ {Γ τs ρ env v term} → NormEnv {Γ} env → NormValue {π τs} v → GoodTerm {τs ++ Γ} {ρ} term → NormCont (applyTuple env v term)
normApplyTuple {v = #tuple values} norm-env norm-values good-term = goodNormClosure (appendNormEnv norm-values norm-env & good-term) ∷ ε

normGetContFoldNat : ∀ {ρ Γ env v term} → NormEnv {Γ} env → NormValue {nat} v → GoodTerm {ρ ∷ Γ} {ρ} term → NormCont (getContFoldNat env v term)
normGetContFoldNat {v = #zero} norm-env norm-value good-term = ε
normGetContFoldNat {v = #succ v} norm-env norm-value good-term = goodNormClosure (norm-env & good-term) ∷ normGetContFoldNat norm-env tt good-term

normApplyFoldNat : ∀ {ρ Γ env v termZ termS} → NormEnv {Γ} env → NormValue {nat} v → GoodTerm {Γ} {ρ} termZ → GoodTerm {ρ ∷ Γ} {ρ} termS → NormCont (applyFoldNat env v termZ termS)
normApplyFoldNat norm-env norm-value good-termZ good-termS = goodNormClosure (norm-env & good-termZ) ∷ normGetContFoldNat norm-env norm-value good-termS

normStepExpr : ∀ {Γ τ expr env} → NormEnv {Γ} env → NormExpr {Γ} {τ} expr → NormVS (stepExpr env expr)
normStepExpr norm-env (normLambda good-term) = normInl \norm-values → good-term (appendNormEnv norm-values norm-env)
normStepExpr norm-env (normCall f xs) = normInr (normApplyFunction (getNormEnv norm-env f) (normMapGet norm-env xs))
normStepExpr norm-env (normInj {τs} {τ} {i} x) = normInl (normInj _ (lem' τs i _ (getNormEnv norm-env x)))
normStepExpr norm-env (normCase x good-terms) = normInr (normApplyCase norm-env (getNormEnv norm-env x) good-terms)
normStepExpr norm-env (normTuple xs) = normInl (normMapGet norm-env xs)
normStepExpr norm-env (normUntuple x good-term) = normInr (normApplyTuple norm-env (getNormEnv norm-env x) good-term)
normStepExpr norm-env normZero = normInl tt
normStepExpr norm-env (normSucc x) = normInl (getNormEnv norm-env x)
normStepExpr norm-env (normFoldNat x good-termz good-terms) = normInr (normApplyFoldNat norm-env (getNormEnv norm-env x) good-termz good-terms)

normComposeCont : ∀ {ρs τ ϕ cont1 cont2} → NormCont {ρs} {τ} cont1 → NormCont {single τ} {ϕ} cont2 → NormCont (composeCont cont1 cont2)
normComposeCont ε norm-cont2 = norm-cont2
normComposeCont (norm-closure ∷ norm-cont1) norm-cont2 = norm-closure ∷ normComposeCont norm-cont1 norm-cont2

normApplyVSCont : ∀ {τ ϕ vs cont} → NormVS {τ} vs → NormCont {single τ} {ϕ} cont → NormVS (applyVSCont vs cont)
normApplyVSCont (normInl norm-value) ε = normInl norm-value
normApplyVSCont {cont = closure@(_ & _) ∷ _} (normInl {value} norm-value) (good-closure ∷ norm-cont) = normInr (good-closure' ∷ norm-cont)
  where
    good-closure' : GoodClosure (applyEnvClosure (value ∷ ε) closure)
    good-closure' {ε} tt = good-closure (norm-value , tt)
normApplyVSCont (normInr norm-cont') norm-cont = normInr (normComposeCont norm-cont' norm-cont)

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
  goodTerm (ret x) {env} norm-env = nex (fin (getNormEnv norm-env x))
  goodTerm (set expr term) {env} norm-env = nex (goodNormVS (normApplyVSCont (normStepExpr norm-env norm-expr) norm-cont))
    where
      norm-expr : NormExpr expr
      norm-expr = normExpr expr

      good-term : GoodTerm term
      good-term = goodTerm term

      norm-cont : NormCont ((env & term) ∷ ε)
      norm-cont = (\norm-values → good-term (appendNormEnv norm-values norm-env)) ∷ ε

result : ∀ {τ vc} → GoodVS {τ} vc → Value τ
result (fin {v} _norm) = v
result (nex c) = result c

eval : ∀ {τ} → Term ε τ → Value τ
eval term = result (goodTerm term tt)

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
  
  test : ℕ → ℕ → Term ε nat
  test n m =
    lambda _ _ (num _ n) ▸
    call _ _ $0 ε ▸
    lambda _ _ (num _ m) ▸
    call _ _ $0 ε ▸
    lambda (nat ∷ nat ∷ ε) _ (add _) ▸
    call _ _ $0 ($1 ∷ $3 ∷ ε) ▸
    ret $0

  _ : Set
  _ = {!eval (test 2 1)!}

{-
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
-}
