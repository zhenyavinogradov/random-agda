module _ where

module _ where
  data ⊥ : Set where
  
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

  ∃ : {A : Set} → (A → Set) → Set
  ∃ {A} B = Σ A B

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

  Eq = _≡_

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

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

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
  _⇒_ : List Type → Type → Type
  σ : List Type → Type
  π : List Type → Type
  nat : Type
  list : Type → Type
  stream : Type → Type

Var : List Type → Type → Set
Var Γ τ = Has Γ τ

module _ (%Expr : Type → Set) (%Abs : List Type → Type → Set) where
  data ExprF : Type → Set where
    lambda : ∀ {ρs τ} → %Abs ρs τ → ExprF (ρs ⇒ τ)
    call   : ∀ {ρs τ} → %Expr (ρs ⇒ τ) → All %Expr ρs → ExprF τ
  
    inj  : ∀ {τs} → Any %Expr τs → ExprF (σ τs)
    case : ∀ {τs ρ} → %Expr (σ τs) → All (\τ → %Abs (single τ) ρ) τs → ExprF ρ
  
    tuple : ∀ {τs} → All %Expr τs → ExprF (π τs)
    untuple : ∀ {τs ρ} → %Expr (π τs) → %Abs τs ρ → ExprF ρ
  
    buildNat : %Expr (σ (π ε ∷ nat ∷ ε)) → ExprF nat
    foldNat : ∀ {ρ} → %Expr nat → %Abs (single (σ (π ε ∷ ρ ∷ ε))) ρ → ExprF ρ
  
    buildList : ∀ {τ} → %Expr (σ (τ ∷ list τ ∷ ε)) → ExprF (list τ)
    foldList : ∀ {τ ρ} → %Expr (list τ) → %Abs (single (σ (τ ∷ ρ ∷ ε))) ρ → ExprF ρ

    buildStream : ∀ {τ ρ} → %Expr ρ → %Abs (single ρ) (π (τ ∷ ρ ∷ ε)) → ExprF (stream τ)
    breakStream : ∀ {τ} → %Expr (stream τ) → ExprF (π (τ ∷ stream τ ∷ ε))

  record DestructDesc : Set₁ where
    constructor _⇒_
    field
      destructData : Set
      destructType : Type → Set

module _ (%Value : Type → Set) (%Closure : List Type → Type → Set) where
  ValueF : Type → Set
  ValueF (ρs ⇒ τ) = %Closure ρs τ
  ValueF (σ τs) = Any %Value τs
  ValueF (π τs) = All %Value τs
  ValueF nat = %Value (σ (π ε ∷ nat ∷ ε))
  ValueF (list τ) = %Value (σ (τ ∷ list τ ∷ ε))
  ValueF (stream τ) = ∃ \ρ → %Value ρ × %Closure (single ρ) (π (τ ∷ ρ ∷ ε))

  DestructF : Type → (Type → Set)
  DestructF (ρs ⇒ τ) = \ϕ → Eq τ ϕ × All %Value ρs
  DestructF (σ τs) = \ϕ → All (\τ → %Closure (single τ) ϕ) τs
  DestructF (π τs) = \ϕ → %Closure τs ϕ
  DestructF nat = \ϕ → %Closure (single (σ (π ε ∷ ϕ ∷ ε))) ϕ
  DestructF (list τ) = \ϕ → %Closure (single (σ (τ ∷ ϕ ∷ ε))) ϕ
  DestructF (stream τ) = \ϕ → Eq (π (τ ∷ stream τ ∷ ε)) ϕ

  data CallStackF : List Type → Type → Set where
    ε   : ∀ {τ} → CallStackF (single τ) τ
    _∷_ : ∀ {ρs τ ϕ} → %Closure ρs τ → CallStackF (single τ) ϕ → CallStackF ρs ϕ

data Term (Γ : List Type) : Type → Set where
  ret : ∀ {τ} → Var Γ τ → Term Γ τ 
  set-value : ∀ {ρ τ} → ExprF (Has Γ) (\ρs τ → Term (ρs ++ Γ) τ) ρ → Term (ρ ∷ Γ) τ → Term Γ τ

module _ (%Value : Type → Set) where
  data ClosureF (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → All %Value Γ → Term (ρs ++ Γ) τ → ClosureF ρs τ


data PrettyTerm (Γ : List Type) (ϕ : Type) : Set where
  wrap : ExprF (\τ → PrettyTerm Γ τ) (\ρs τ → PrettyTerm (ρs ++ Γ) τ) ϕ → PrettyTerm Γ ϕ
  --lett : ∀ {ρ} → PrettyTerm Γ ρ → PrettyTerm (ρ ∷ Γ) ϕ → PrettyTerm Γ ϕ

mutual
  record Value (τ : Type) : Set where
    inductive
    constructor wrap
    field unwrap : ValueF Value Closure τ

  record Closure (ρs : List Type) (τ : Type) : Set where
    inductive
    constructor wrap
    field unwrap : ClosureF Value ρs τ
open Value public
open Closure public

AllValue : List Type → Set
AllValue ε = ⊤
AllValue (τ ∷ τs) = Value τ × AllValue τs

AnyValue : List Type → Set
AnyValue ε = ⊥
AnyValue (τ ∷ τs) = Value τ + AnyValue τs

CallStack : List Type → Type → Set
CallStack = CallStackF Value Closure

applyClosure : ∀ {ρs τ} → Closure ρs τ → All Value ρs → Closure ε τ
applyClosure (wrap (env & term)) values = wrap ((values ++' env) & term)

stepExpr : ∀ {τ} → ExprF Value Closure τ → Value τ + CallStack ε τ
stepExpr (lambda c) = inl (wrap c)
stepExpr (inj x) = inl (wrap x)
stepExpr (tuple xs) = inl (wrap xs)
stepExpr (buildNat f) = inl (wrap f)
stepExpr (buildList f) = inl (wrap f)
stepExpr (buildStream x f) = inl (wrap (_ ,, (x , f)))
stepExpr (call (wrap c) xs) = inr (applyClosure c xs ∷ ε)
stepExpr (case (wrap x) cs) = inr ({!applyClosure !} ∷ ε)
stepExpr (untuple (wrap xs) c) = inr (applyClosure c xs ∷ ε)
stepExpr (foldNat (wrap x) f) = inr {!applyClosure f (x ∷ ε)!}
stepExpr (foldList (wrap x) f) = inr {!applyClosure f (x ∷ ε)!}
stepExpr (breakStream (wrap (ρ ,, (x , f)))) = inr {!applyClosure f (x ∷ ε)!}

step : ∀ {τ} → CallStack ε τ → Value τ + CallStack ε τ
step = {!!}

{-
mutual
  Env : List Type → Set
  Env Γ = All Value Γ
  
  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → Term (ρs ++ Γ) τ → Closure ρs τ

data Cont : List Type → Type → Set where
  ε : ∀ {ρ} → Cont (single ρ) ρ
  _∷_ : ∀ {ρs ϕ τ} → Closure ρs ϕ → Cont (single ϕ) τ → Cont ρs τ

VS : Type → Set
VS τ = Value τ + Cont ε τ
-}

{-
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
  
stepExpr : ∀ {Γ τ} → Env Γ → ExprF Γ τ → Value τ + Cont ε τ
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
-}
