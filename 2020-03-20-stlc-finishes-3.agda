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

{-
mutual
  --{-# NO_POSITIVITY_CHECK #-} -- inductive on τ
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
  -}

record PredVS (τ : Type) : Set₁ where
  constructor mkPredVS
  field getPredVS : VS τ → Set
open PredVS public

data Ends {S V : Set} (step : S → V + S) (End : V → Set) : V + S → Set where
  fin : ∀ v → End v → Ends step End (inl v)
  nex : ∀ s → Ends step End (step s) → Ends step End (inr s)

data FinishesF {τ} (P : PredVS τ) : VS τ → Set where
  fin : ∀ {v} → getPredVS P (inl v) → FinishesF P (inl v)
  nex : ∀ {s} → FinishesF P (step s) → FinishesF P (inr s)

data All₁ {A : Set} (P : A → Set₁) : List A → Set₁ where
  ε : All₁ P ε
  _∷_ : ∀ {a as} → P a → All₁ P as → All₁ P (a ∷ as)

AllPredVS : List Type → Set₁
AllPredVS τs = All₁ PredVS τs

runAllPredVS : ∀ {ρs} → AllPredVS ρs → Env ρs → Set
runAllPredVS ε ε = ⊤
runAllPredVS (P ∷ Ps) (value ∷ env) = getPredVS P (inl value) × runAllPredVS Ps env

getAllPredVS : ∀ {τs τ} → AllPredVS τs → Has τs τ → Value τ → Set
getAllPredVS (P ∷ Ps) here value = getPredVS P (inl value)
getAllPredVS (P ∷ Ps) (there i) value = getAllPredVS Ps i value

NormEnvF : ∀ {τs} → AllPredVS τs → Env τs → Set
NormEnvF ε ε = ⊤
NormEnvF (P ∷ Ps) (value ∷ values) = getPredVS P (inl value) × NormEnvF Ps values

GoodClosureF : ∀ {ρs τ} → AllPredVS ρs → PredVS τ → Closure ρs τ → Set
GoodClosureF {ρs} {τ} Fin-ρs Fin-τ closure = ∀ {values} → NormEnvF {ρs} Fin-ρs values → getPredVS Fin-τ (inr (applyEnvClosure values closure ∷ ε))

NormValue-⇒ : ∀ {ρs τ} → (Fin-ρs : AllPredVS ρs) (Fin-τ : PredVS τ) → Value (ρs ⇒ τ) → Set
NormValue-⇒ Fin-ρs Fin-τ (#closure cl) = GoodClosureF Fin-ρs Fin-τ cl

NormValue-π : ∀ {τs} → (Fin-τs : AllPredVS τs) → Value (π τs) → Set
NormValue-π Fin-τs (#tuple vs) = runAllPredVS Fin-τs vs

NormValue-σ : ∀ {τs} → (Fin-τs : AllPredVS τs) → Value (σ τs) → Set
NormValue-σ Fin-τs (#inj i v) = getAllPredVS Fin-τs i v

NormValue-nat : Value nat → Set
NormValue-nat value = ⊤

mutual
  GoodVS : (τ : Type) → PredVS τ
  GoodVS (ρs ⇒ τ) = mkPredVS (Ends (step {ρs ⇒ τ}) (NormValue-⇒ (NormEnv* ρs) (GoodVS τ)))
  GoodVS (σ τs) = mkPredVS (Ends (step {σ τs}) (NormValue-σ (NormEnv* τs)))
  GoodVS (π τs) = mkPredVS (Ends (step {π τs}) (NormValue-π (NormEnv* τs)))
  GoodVS nat = mkPredVS (Ends (step {nat}) NormValue-nat)
  
  NormEnv* : (τs : List Type) → AllPredVS τs
  NormEnv* ε = ε
  NormEnv* (τ ∷ τs) = GoodVS τ ∷ NormEnv* τs

Finishes : {τ : Type} → VS τ → Set
Finishes {τ} vs = getPredVS (GoodVS τ) vs

NormValue : (τ : Type) → Value τ → Set
NormValue τ value = Finishes (inl value)
  
GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set
GoodClosure {ρs} {τ} = GoodClosureF (NormEnv* ρs) (GoodVS τ)

{-
Finishes = GoodVS

step : ∀ {τ} → Cont ε τ → VS τ

GoodVS      : ∀ {τ}    → VS τ → Set
GoodCont    : ∀ {ρs τ} → Cont ρs τ → Set
GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set
GoodTerm    : ∀ {Γ τ}  → Term Γ τ → Set
NormValue   : ∀ {τ}    → Value τ → Set
NormGet     : ∀ {τs τ} → Has τs τ → Value τ → Set
NormEnv     : ∀ {τs}   → Env τs → Set
NormClosure : ∀ {ρs τ} → Closure ρs τ → Set
NormExpr    : ∀ {Γ τ}  → Expr Γ τ → Set
NormCont    : ∀ {ρs τ} → Cont ρs τ → Set
NormVS      : ∀ {τ}    → VS τ → Set
-}
