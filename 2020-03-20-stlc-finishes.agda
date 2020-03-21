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

  data Bool : Set where
    false true : Bool

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
  _⇒_ : Type → Type → Type
  bool : Type

Context : Set
Context = List Type

Var : Context → Type → Set
Var Γ τ = Has Γ τ

mutual
  data Expr (Γ : Context) : Type → Set where
    lambda : (ρ τ : Type) → Term (ρ ∷ Γ) τ → Expr Γ (ρ ⇒ τ)
    call : (ρ τ : Type) → Var Γ (ρ ⇒ τ) → Var Γ ρ → Expr Γ τ
    true : Expr Γ bool
    false : Expr Γ bool
    case : (ρ : Type) → Var Γ bool → Term Γ ρ → Term Γ ρ → Expr Γ ρ

  data Term : Context → Type → Set where
    ret : ∀ {Γ τ} → Var Γ τ → Term Γ τ 
    set : ∀ {Γ ρ τ} → Expr Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ

mutual
  data Value : Type → Set where
    #closure : ∀ {ρ τ} → Closure (single ρ) τ → Value (ρ ⇒ τ)
    #false : Value bool
    #true : Value bool

  Env : Context → Set
  Env Γ = All Value Γ
  
  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → Term (ρs ++ Γ) τ → Closure ρs τ

data Cont : List Type → Type → Set where
  ε : ∀ {ρ} → Cont (single ρ) ρ
  _∷_ : ∀ {ρs ϕ τ} → Closure ρs ϕ → Cont (single ϕ) τ → Cont ρs τ

applyFunction : ∀ {ρ τ} → Value (ρ ⇒ τ) → Value ρ → Cont ε τ
applyFunction (#closure (envf & termf)) v = (v ∷ envf) & termf ∷ ε

applyBool : ∀ {Γ ρ} → Env Γ → Value bool → Term Γ ρ → Term Γ ρ → Cont ε ρ
applyBool env #false termFalse termTrue = (env & termFalse) ∷ ε
applyBool env #true termFalse termTrue = (env & termTrue) ∷ ε

stepExpr : ∀ {Γ τ} → Env Γ → Expr Γ τ → Value τ + Cont ε τ
stepExpr env (lambda ρs τ term) = inl (#closure (env & term))
stepExpr env (call ρs τ f x) = inr (applyFunction (get env f) (get env x))
stepExpr env true = inl #true
stepExpr env false = inl #false
stepExpr env (case ρ x termFalse termTrue) = inr (applyBool env (get env x) termFalse termTrue)

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
{-
  --{-# NO_POSITIVITY_CHECK #-} -- inductive on τ
  data Fin0 : ∀ {τ} → VS τ → Set where
    fin : ∀ {τ v} → Norm τ v → Fin0 (inl v)
    nex : ∀ {τ s} → Fin0 {τ} (step s) → Fin0 (inr s)

  data FinR (S V : Set) (st : S → V + S) (NV : V → Set) : V + S → Set where
    fin : ∀ {v} → NV v → FinR S V st NV (inl v)
    nex : ∀ {s} → FinR S V st NV (st s) → FinR S V st NV (inr s)

  --FinSm : (τ : Type) → Set
  --FinSm (ρ ⇒ τ) = VS ρ → Set

  FinType : (τ : Type) → VS τ → Set
  FinType τ = FinR (Cont ε τ) (Value τ) (step {τ}) (Norm τ)

  Fin : (τ : Type) → VS τ → Set
  Fin (ρ ⇒ τ) = {!FinType!}
  Fin bool = FinType bool

  Norm : (τ : Type) → Value τ → Set
  Norm (ρ ⇒ τ) (#closure (env & term)) = ∀ {value} → Norm ρ value → Fin* (inr (((value ∷ env) & term) ∷ ε))
    where
      Fin* : VS τ → Set
      Fin* = FinType τ
  Norm bool _ = ⊤
  -}

  apply : ∀ {ρ τ} → Value ρ → Closure (single ρ) τ → Cont ε τ
  apply v (env & term) = ((v ∷ env) & term) ∷ ε

{-
  data Fin : (τ : Type) → VS τ → Set where
    fin-⇒    : ∀ {ρ τ cl} → (∀ v → Fin ρ (inl v) → Fin τ (apply v cl)) → Fin (ρ ⇒ τ) (inl (#closure cl))
    fin-bool : ∀ v → Fin bool (inl v)
    nex      : ∀ {τ s} → Fin τ (step s) → Fin τ (inr s)
    -}

record PredVS (τ : Type) : Set₁ where
  constructor mkPredVS
  field applyPredVS : VS τ → Set
open PredVS

{-
data Fin-bool : VS bool → Set where
  fin-bool : ∀ v → Fin-bool (inl v)
  nex-bool : ∀ s → Fin-bool (step s) → Fin-bool (inr s)

data Fin-⇒ (ρ τ : Type) (Fin-ρ : PredVS ρ) (Fin-τ : PredVS τ) : VS (ρ ⇒ τ) → Set where
  fin-⇒ : ∀ cl → (∀ v → applyPredVS Fin-ρ (inl v) → applyPredVS Fin-τ (apply v cl)) → Fin-⇒ ρ τ Fin-ρ Fin-τ (inl (#closure cl))
  nex-⇒ : ∀ s → Fin-⇒ ρ τ Fin-ρ Fin-τ (step s) → Fin-⇒ ρ τ Fin-ρ Fin-τ (inr s)
  -}

data Ends {S V : Set} (step : S → V + S) (End : V → Set) : V + S → Set where
  fin : ∀ v → End v → Ends step End (inl v)
  nex : ∀ s → Ends step End (step s) → Ends step End (inr s)

NormValue-⇒ : {ρ τ : Type} (Fin-ρ : PredVS ρ) (Fin-τ : PredVS τ) → Value (ρ ⇒ τ) → Set
NormValue-⇒ Fin-ρ Fin-τ (#closure cl) = ∀ v → applyPredVS Fin-ρ (inl v) → applyPredVS Fin-τ (inr (apply v cl))

Fin-⇒ : (ρ τ : Type) (Fin-ρ : PredVS ρ) (Fin-τ : PredVS τ) → VS (ρ ⇒ τ) → Set
Fin-⇒ ρ τ Fin-ρ Fin-τ = Ends (step {ρ ⇒ τ}) (NormValue-⇒ Fin-ρ Fin-τ)

Fin-bool : VS bool → Set
Fin-bool = Ends (step {bool}) End
  where
    End : Value bool → Set
    End v = ⊤

FinI : (τ : Type) → PredVS τ
FinI (ρ ⇒ τ) = mkPredVS (Fin-⇒ ρ τ (FinI ρ) (FinI τ))
FinI bool = mkPredVS Fin-bool


--Norm : (τ : Type) → Value τ → Set
--Norm (ρ ⇒ τ) = NormF (ρ ⇒ τ) (preds⇒ (Norm ρ) (Norm τ))
--Norm bool = NormF bool predsbool

{-
  --data FinF (τ : Type) (N : Value τ → Set) : VS τ → Set where
  data FinF (τ : Type) (N : Value τ → Set) : VS τ → Set where
    fin : ∀ {v} → N v → FinF τ N (inl v)
    nex : ∀ {s} → FinF τ N (step s) → FinF τ N (inr s)

  NormF : (τ : Type) → Preds τ → Value τ → Set
  NormF (ρ ⇒ τ) (preds⇒ Norm-ρ Norm-τ) (#closure (env & term)) = ∀ {value} → Norm-ρ value → FinF τ Norm-τ (inr (((value ∷ env) & term) ∷ ε))
  NormF bool _ _ = ⊤

  Norm : (τ : Type) → Value τ → Set
  Norm (ρ ⇒ τ) = NormF (ρ ⇒ τ) (preds⇒ (Norm ρ) (Norm τ))
  Norm bool = NormF bool predsbool
  -}
