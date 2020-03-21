module _ where

module _ where
  record ⊤ : Set where

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

  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → Term (ρs ++ Γ) τ → Closure ρs τ
  
  Env : Context → Set
  Env Γ = All (\τ → Value τ) Γ

ClosureN : Type → Set
ClosureN τ = Closure ε τ

ClosureF : Type → Type → Set
ClosureF ρ τ = Closure (single ρ) τ

-- refl-trans closure of ClosureF
data Cont (ρ : Type) : Type → Set where
  ε : Cont ρ ρ
  -- _∷_ : ∀ {ϕ τ} → ClosureF ρ ϕ → Cont ϕ τ → Cont ρ τ
  _∷_ : ∀ {ϕ τ} → ClosureF ρ ϕ → Cont ϕ τ → Cont ρ τ

-- trans closure of ClosureF
data S' (ρ τ : Type) : Set where
  $' : ∀ {ϕ} → ClosureF ρ ϕ → Cont ϕ τ → S' ρ τ

data S (τ : Type) : Set where
  $ : ∀ {ϕ} → ClosureN ϕ → Cont ϕ τ → S τ

VS : Type → Set
VS τ = Value τ + S τ

data Cont* : List Type → Type → Set where
  ε : ∀ {ρ} → Cont* (single ρ) ρ
  -- _∷_ : ∀ {ϕ τ} → ClosureF ρ ϕ → Cont ϕ τ → Cont ρ τ
  _∷_ : ∀ {ρs ϕ τ} → Closure ρs ϕ → Cont* (single ϕ) τ → Cont* ρs τ

data S* (ρs : List Type) (τ : Type) : Set where
  $$ : ∀ {ϕ} → Closure ρs ϕ → Cont* (single ϕ) τ → S* ρs τ

composeCont* : ∀ {ρs ϕ τ} → Cont* ρs ϕ → Cont* (single ϕ) τ → Cont* ρs τ
composeCont* ε cont2 = cont2
composeCont* (cl1 ∷ cont1) cont2 = cl1 ∷ composeCont* cont1 cont2

S*ToCont* : ∀ {ρs τ} → S* ρs τ → Cont* ρs τ
S*ToCont* ($$ cl cont) = cl ∷ cont

closureToCont* : ∀ {ρs τ} → Closure ρs τ → Cont* ρs τ
closureToCont* cl = cl ∷ ε

stepExpr : ∀ {Γ τ} → Env Γ → Expr Γ τ → VS τ
stepExpr env (lambda ρs τ term) = inl (#closure (env & term))
stepExpr env (call ρs τ f xs) = inr (gets (get env f))
  where
    gets : Value (ρs ⇒ τ) → S τ
    gets (#closure (envf & termf)) = $ ((mapAll (get env) xs ++' envf) & termf) ε
stepExpr env (inj τs τ i x) = inl (#inj i (get env x))
stepExpr env (case τs ρ x terms) = inr (gets (get env x))
  where
    gets : Value (σ τs) → S ρ
    gets (#inj i v) = $ ((v ∷ env) & (get terms i)) ε
stepExpr env (tuple τs xs) = inl (#tuple (mapAll (get env) xs))
stepExpr env (untuple τs ρ x term) = inr (gets (get env x))
  where
    gets : Value (π τs) → S ρ
    gets (#tuple vs) = $ ((vs ++' env) & term) ε
stepExpr env zero = inl #zero
stepExpr env (succ x) = inl (#succ (get env x))
stepExpr env (foldNat ρ x termz terms) = inr (gets (get env x))
  where
    getcont : Value nat → Cont ρ ρ
    getcont #zero = ε
    getcont (#succ n) = env & terms ∷ getcont n

    gets : Value nat → S ρ
    gets n = $ (env & termz) (getcont n)

NormTerm : ∀ {Γ τ} → Term Γ τ → Set
NormTerm = {!!}

data NormExpr {Γ} : ∀ {τ} → Expr Γ τ → Set where
  normLambda : ∀ {ρs τ term} → NormTerm term → NormExpr (lambda ρs τ term)
  normCall : ∀ {ρs τ f xs} → NormExpr (call ρs τ f xs)
  normInj : ∀ {τs τ i x} → NormExpr (inj τs τ i x)
  normCase : ∀ {τs ρ x terms} → All2 NormTerm terms → NormExpr (case τs ρ x terms)
  normTuple : ∀ {τs xs} → NormExpr (tuple τs xs)
  normUntuple : ∀ {τs ρ x term} → NormTerm term → NormExpr (untuple τs ρ x term)
  normZero : NormExpr zero
  normSucc : ∀ {x} → NormExpr (succ x)
  normFoldNat : ∀ {ρ x termz terms} → NormTerm termz → NormTerm terms → NormExpr (foldNat ρ x termz terms)

composeCont : ∀ {ϕ ρ τ} → Cont ϕ ρ → Cont ρ τ → Cont ϕ τ
composeCont ε c2 = c2
composeCont (envTerm ∷ c1) c2 = envTerm ∷ composeCont c1 c2

composeSCont : ∀ {ρ τ} → S ρ → Cont ρ τ → S τ
composeSCont ($ envTerm cont) cont' = $ envTerm (composeCont cont cont')

applyVClosureF : ∀ {ρ τ} → Value ρ → ClosureF ρ τ → ClosureN τ
applyVClosureF v (env & term) = (v ∷ env) & term

envTermToS : ∀ {τ} → ClosureN τ → S τ
envTermToS envTerm = $ envTerm ε

envTerm'ToCont : ∀ {ρ τ} → ClosureF ρ τ → Cont ρ τ
envTerm'ToCont envTerm' = envTerm' ∷ ε

applyVsClosureF : ∀ {ρ τ} → VS ρ → ClosureF ρ τ → S τ
applyVsClosureF (inl v) envTerm' = envTermToS (applyVClosureF v envTerm')
applyVsClosureF (inr s) envTerm' = composeSCont s (envTerm'ToCont envTerm')

stepClosureN : ∀ {τ} → ClosureN τ → VS τ
stepClosureN (env & ret x) = inl (get env x)
stepClosureN (env & set expr term) = inr (applyVsClosureF (stepExpr env expr) (env & term))

applyVCont : ∀ {ρ τ} → Value ρ → Cont ρ τ → VS τ
applyVCont v ε = inl v
applyVCont v (envTerm ∷ cont) = inr ($ (applyVClosureF v envTerm) cont)

applyVsCont : ∀ {ρ τ} → VS ρ → Cont ρ τ → VS τ
applyVsCont (inl v) cont = applyVCont v cont
applyVsCont (inr s) cont = inr (composeSCont s cont)

step : ∀ {τ} → S τ → VS τ
step ($ envTerm cont) = applyVsCont (stepClosureN envTerm) cont


data IsLeft {A B : Set} : A + B → Set where
  isLeft : {a : A} → IsLeft (inl a)

data IsRight {A B : Set} : A + B → B → Set where
  isRight : {b : B} → IsRight (inr b) b

data FinishesS {τ : Type} : S τ → Set where
  fin : ∀ {s : S τ} → IsLeft (step s) → FinishesS s
  nex : ∀ {s} s' → IsRight (step s) s' → FinishesS s' → FinishesS s

data FinishesVS {τ : Type} : VS τ → Set where
  finv : ∀ {v} → FinishesVS (inl v)
  nexv : ∀ {s} → FinishesVS (step s) → FinishesVS (inr s)

{-# TERMINATING #-} -- induction on type τ
NormValue : ∀ {τ} → Value τ → Set
NormValue {ρs ⇒ τ} (#closure (env & term)) = (args : Env ρs) → All2 NormValue args → FinishesS ($ ((args ++' env) & term) ε)
NormValue {σ τs} (#inj i v) = NormValue v
NormValue {π τs} (#tuple vs) = All2 NormValue vs
NormValue {nat} #zero = ⊤
NormValue {nat} (#succ v) = NormValue v 

NormEnv : ∀ {Γ} → Env Γ → Set
NormEnv env = All2 NormValue env

normExpr : ∀ {Γ τ env expr} → NormEnv {Γ} env → NormExpr {Γ} {τ} expr → FinishesVS (stepExpr env expr)
normExpr normEnv (normLambda _) = {!!}
normExpr normEnv normCall = {!!}
normExpr normEnv normInj = finv
normExpr normEnv (normCase x) = {!!}
normExpr normEnv normTuple = finv
normExpr normEnv (normUntuple x) = {!!}
normExpr normEnv normZero = finv
normExpr normEnv normSucc = finv
normExpr normEnv (normFoldNat x x₁) = {!!}

NormClosureN : ∀ {τ} → ClosureN τ → Set
NormClosureN envTerm = FinishesS (envTermToS envTerm) 

NormClosureF : ∀ {ρ τ} → ClosureF ρ τ → Set
NormClosureF {ρ} {τ} envTerm' = ∀ {v} → NormValue {ρ} v → NormClosureN (applyVClosureF v envTerm')

data NormClosure {ρs τ} : Closure ρs τ → Set where


data NormCont {ρ} : ∀ {τ} → Cont ρ τ → Set where
  normNil : NormCont ε
  normCons
    : ∀ {ϕ τ envTerm' cont}
    → NormClosureF {ρ} {ϕ} envTerm' → NormCont {ϕ} {τ} cont → NormCont (envTerm' ∷ cont)

data ExprRes (τ : Type) : Set where
  rval : Value τ → ExprRes τ
  rrun : ∀ {ρ} → Closure ε ρ → Cont ρ τ → ExprRes τ

data NormExprRes {τ : Type} : ExprRes τ → Set where
  nrval : ∀ {v} → NormValue v → NormExprRes (rval v)
  nrrun : ∀ {ρ cl cont} → NormClosure {ε} {ρ} cl → NormCont ρ τ → NormExprRes (rrun cl cont)

FinishesCont : ∀ {ρ τ} → Cont ρ τ → Set
FinishesCont cont = ∀ v → NormValue v → FinishesVS (applyVCont v cont)

appendFinishesCont : ∀ {ϕ ρ τ} envTerm' → NormClosureF {ϕ} {ρ} envTerm' → ∀ cont → FinishesCont {ρ} {τ} cont → FinishesCont (envTerm' ∷ cont)
appendFinishesCont envTerm' normClosureF cont normCont v normV =
  {!normClosureF normV!}

composeFinishesCont : ∀ {ϕ ρ τ} cont1 → FinishesCont {ϕ} {ρ} cont1 → ∀ cont2 → FinishesCont {ρ} {τ} cont2 → FinishesCont (composeCont cont1 cont2)
composeFinishesCont ε normCont1 cont2 normCont2 = normCont2
composeFinishesCont (envTerm'1 ∷ cont1) normCont1 cont2 normCont2 = {!!}

applyVClosure : ∀ {ρs τ} → All Value ρs → Closure ρs τ → S τ
applyVClosure vs (env & term) = $ ((vs ++' env) & term) ε

applyVCont* : ∀ {ρs τ} → All Value ρs → Cont* ρs τ → VS τ
applyVCont* vs ((env & term) ∷ cont) = inr ($ ((vs ++' env) & term) {!cont!})
applyVCont* (v ∷ ε) ε = inl v

NormClosure : ∀ {ρs τ} → Closure ρs τ → Set
NormClosure cl = ∀ {vs} → All2 NormValue vs → FinishesS (applyVClosure vs cl)

data NormCont* : ∀ {ρs τ} → Cont* ρs τ → Set where
  normNil : ∀ {τ} → NormCont* {single τ} {τ} ε
  normCons
    : ∀ {ρs ϕ τ cl cont}
    → NormClosure {ρs} {ϕ} cl → NormCont* {single ϕ} {τ} cont → NormCont* (cl ∷ cont)

FinishesCont* : ∀ {ρs τ} → Cont* ρs τ → Set
FinishesCont* cont = ∀ vs → All2 NormValue vs → FinishesVS (applyVCont* vs cont)

lemNormCont* : ∀ {ρs τ} → (cont : Cont* ρs τ) → NormCont* cont → FinishesCont* cont
lemNormCont* ε normCont v normV = {!!}
lemNormCont* (clF ∷ cont) (normCons normClF normCont) v normV = {!!}

-- lemNormCont : ∀ {ρ τ} → (cont : Cont ρ τ) → NormCont cont → FinishesCont cont
-- lemNormCont ε normCont v normV = finv
-- lemNormCont (envTerm' ∷ cont) (normCons normClosureF normCont) v normV =
  {!normClosureF!}

normTerm : ∀ {Γ τ} env term → NormEnv {Γ} env → FinishesS {τ} ($ (env & term) ε)
normTerm = {!!}

norm : ∀ {Γ ρ τ} env term cont → NormEnv {Γ} env → NormCont {ρ} {τ} cont → FinishesS ($ (env & term) cont)
norm = {!!}

evalVS : ∀ {τ} → (vs : VS τ) → FinishesVS vs → Value τ
evalVS (inl v) finv = v
evalVS (inr s) (nexv f) = evalVS (step s) f

evalTerm : ∀ {τ} → Term ε τ → Value τ
evalTerm term = {!!}

eval : ∀ {Γ τ ρ} → Env Γ → Term Γ τ → Cont τ ρ → Value ρ
eval env (ret x) ε = get env x
eval env (ret x) ((env' & term) ∷ cont) = eval (get env x ∷ env') term cont
eval env (set (lambda ρs τ termf) term) cont = eval (#closure (env & termf) ∷ env) term cont
eval env (set (call ρs τ f xs) term) cont with get env f
... | #closure (envf & termf) = eval {!!} termf {!!}
eval env (set (inj τs τ x x₁) term) cont = {!!}
eval env (set (case τs ρ x x₁) term) cont = {!!}
eval env (set (tuple τs x) term) cont = {!!}
eval env (set (untuple τs ρ x x₁) term) cont = {!!}
eval env (set zero term) cont = {!!}
eval env (set (succ x) term) cont = {!!}
eval env (set (foldNat ρ x x₁ x₂) term) cont = {!!}
