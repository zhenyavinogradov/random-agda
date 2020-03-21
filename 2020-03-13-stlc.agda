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
  list : Type → Type
  stream : Type → Type

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

infixr 5 _▸_
_▸_ : ∀ {Γ ρ τ} → Expr Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ
_▸_ = set

mutual
  data Value : Type → Set where
    #closure
      : (ρs : List Type) (τ : Type)
      → {Γ : List Type} → (env : Env Γ) → (term : Term (ρs ++ Γ) τ) → Value (ρs ⇒ τ)
    #tuple
      : (τs : List Type)
      → All Value τs → Value (π τs)
    #inj
      : (τs : List Type) (τ : Type) (_ : Has τs τ)
      → Value τ → Value (σ τs)
    #zero : Value nat
    #succ : Value nat → Value nat
  
  Env : Context → Set
  Env Γ = All (\τ → Value τ) Γ

{-
step : S → Value + S
run : S → Value

eval : Env, Term → Value
-- _ : Env, Term → Value + (Env, Term)
_ : Env, Expr → Value + (Env, Term)

Cont:
- nil
- cons (Env, Term, Cont)

S:
- apply (Value, Cont)
- run ((Env, Term), Cont)

single:
(e,t) → value

[(e,t)]

steps:
(e₁,t₁), (e₂,t₂), (e₃,t₃), …, (eₙ,tₙ) → value
-}

data Cont (ρ : Type) : Type → Set where
  nil : Cont ρ ρ
  cons : {ϕ τ : Type} → {Γ : Context} → (env : Env Γ) → (term : Term (ρ ∷ Γ) ϕ) → Cont ϕ τ → Cont ρ τ
 
data S (τ : Type) : Set where
  $ : ∀ {Γ ρ} → Env Γ → Term Γ ρ → Cont ρ τ → S τ

data S' (ϕ : Type) (τ : Type) : Set where
  $' : ∀ {Γ ρ} → Env Γ → Term (ϕ ∷ Γ) ρ → Cont ρ τ → S' ϕ τ

VS : Type → Set
VS τ = Value τ + S τ

stepExpr : ∀ {Γ τ} → Env Γ → Expr Γ τ → VS τ
stepExpr env (lambda ρs τ term) = inl (#closure _ _ env term)
stepExpr env (call ρs τ f xs) = inr (gets (get env f))
  where
    gets : Value (ρs ⇒ τ) → S τ
    gets (#closure _ _ envf termf) = $ (mapAll (get env) xs ++' envf) termf nil
stepExpr env (inj τs τ i x) = inl (#inj _ _ i (get env x))
stepExpr env (case τs ρ x terms) = inr (gets (get env x))
  where
    gets : Value (σ τs) → S ρ
    gets (#inj _ _ i v) = $ (v ∷ env) (get terms i) nil
stepExpr env (tuple τs xs) = inl (#tuple _ (mapAll (get env) xs))
stepExpr env (untuple τs ρ x term) = inr (gets (get env x))
  where
    gets : Value (π τs) → S ρ
    gets (#tuple _ vs) = $ (vs ++' env) term nil
stepExpr env zero = inl #zero
stepExpr env (succ x) = inl (#succ (get env x))
stepExpr env (foldNat ρ x termz terms) = inr ($ env termz (getcont (get env x)))
  where
    getcont : Value nat → Cont _ _
    getcont #zero = nil
    getcont (#succ n) = cons env terms (getcont n)

applyCont : ∀ {ϕ τ} → Cont ϕ τ → Value ϕ → VS τ
applyCont nil v = inl v
applyCont (cons env term cont) v = inr ($ (v ∷ env) term cont)

composeCont : ∀ {ϕ ρ τ} → Cont ϕ ρ → Cont ρ τ → Cont ϕ τ
composeCont nil c2 = c2
composeCont (cons env term c1) c2 = cons env term (composeCont c1 c2)

compose : ∀ {ρ τ} → VS ρ → S' ρ τ → S τ
compose (inl v) ($' env term cont) = $ (v ∷ env) term cont
compose (inr ($ env' term' cont')) ($' env term cont) = $ env' term' (composeCont cont' (cons env term cont))

step : {τ : Type} → S τ → VS τ
step ($ env (ret x) cont) = applyCont cont (get env x)
step ($ env (set expr term) cont) = inr (compose (stepExpr env expr) ($' env term cont))

{-

put : ∀ {ϕ Γ ρ τ} → Value ϕ → Env Γ → Term (ϕ ∷ Γ) ρ → Cont ρ τ → S τ
put v env term cont = $ (v ∷ env) term cont

fcall : ∀ {Γ τ Δ τ' τ''} → Env Γ → Term Γ τ → Env Δ → Term (τ ∷ Δ) τ' → Cont τ' τ'' → S τ''
fcall env' term' env term cont = $ env' term' (cons env term cont)

step : {τ : Type} → S τ → Value τ + S τ
step ($ env (ret x) nil) =
  let vx = get env x
  in inl vx
step ($ env (ret x) (cons env' term cont)) =
  let vx = get env x
  in inr (put vx env' term cont)

step ($ env (set (lambda ρs τ term') term) cont) =
  inr (put (#closure ρs τ env term') env term cont)
{-
step {ϕ} ($ env (set (call ρs τ f xs) term) cont) =
  foo (get env f)
  where
    foo : Value (ρs ⇒ τ) → Value ϕ + S ϕ
    foo (#closure .ρs .τ envf termf) =
      let vxs = mapAll (get env) xs
      in inr (fcall (vxs ++' envf) termf env term cont)
-}
step ($ env (set (call ρs τ f xs) term) cont) with get env f
… | #closure .ρs .τ envf termf =
  let vxs = mapAll (get env) xs
  in inr (fcall (vxs ++' envf) termf env term cont)
{-
step ($ env (set (call ρs τ f xs) term) cont) =
  inr (
    get env f € \{ (#closure ρs τ envf termf) →
    let vxs = mapAll (get env) xs
    in fcall (vxs ++' envf) termf env term cont
    }
  )
  -}

step ($ env (set (inj τs τ i x) term) cont) =
  let vx = get env x
  in inr (put (#inj τs τ i vx) env term cont)
step ($ env (set (case τs ρ x terms) term) cont) =
  get env x € \{ (#inj τs τ i vx) →
  let termi = get terms i
  in inr (fcall (vx ∷ env) termi env term cont)
  }
step ($ env (set (tuple τs xs) term) cont) =
  let vxs = mapAll (get env) xs
  in inr (put (#tuple τs vxs) env term cont)
step ($ env (set (untuple τs ρ x term') term) cont) =
  get env x € \{ (#tuple τs vs) →
  inr (fcall (vs ++' env) term' env term cont)
  }

step ($ env (set zero term) cont) =
  inr (put #zero env term cont)
step ($ env (set (succ x) term) cont) =
  let vx = get env x
  in inr (put (#succ vx) env term cont)
step ($ env (set (foldNat ρ x termz terms) term) cont) =
  let vx = get env x
  in inr ($ env termz (getcont vx))
  where
    getcont : Value nat → Cont _ _
    getcont #zero = cons env term cont
    getcont (#succ n) = cons env terms (getcont n)
    -}

{-
step ($ env (ret x) nil) =
  let vx = get env x
  in inl vx
step ($ env (ret x) (cons env' term cont)) =
  let vx = get env x
  in inr ($ (vx ∷ env') term cont)
step ($ env (set (lambda ρs τ term') term) cont) =
  inr ($ (#closure ρs τ env term' ∷ env) term cont)
step ($ env (set (call ρs τ f xs) term) cont) =
  get env f € \{ (#closure ρs τ envf termf) →
  let vxs = mapAll (get env) xs
  in inr ($ (vxs ++' envf) termf (cons env term cont))
  }
step ($ env (set (inj τs τ i x) term) cont) =
  let vx = get env x
  in inr ($ ((#inj τs τ i vx) ∷ env) term cont)
step ($ env (set (case τs ρ x terms) term) cont) =
  get env x € \{ (#inj τs τ i vx) →
  let termi = get terms i
  in inr ($ (vx ∷ env) termi (cons env term cont))
  }
step ($ env (set (tuple τs xs) term) cont) =
  let vxs = mapAll (get env) xs
  in inr ($ ((#tuple τs vxs) ∷ env) term cont)
step ($ env (set (untuple τs ρ x term') term) cont) =
  get env x € \{ (#tuple τs vs) →
  inr ($ (vs ++' env) term' (cons env term cont))
  }

step ($ env (set zero term) cont) =
  inr ($ (#zero ∷ env) term cont)
step ($ env (set (succ x) term) cont) =
  let vx = get env x
  in inr ($ (#succ vx ∷ env) term cont)
step ($ env (set (foldNat ρ x termz terms) term) cont) =
  let vx = get env x
  in inr ($ env termz (getcont vx))
  where
    getcont : Value nat → Cont _ _
    getcont #zero = cons env term cont
    getcont (#succ n) = cons env terms (getcont n)
    -}

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

stepn : {τ : Type} → ℕ → S τ → Value τ + S τ
stepn zero s = inr s
stepn (succ n) s with step s
… | inl v = inl v
… | inr s' = stepn n s'

run : ∀ {τ} → ℕ → Term ε τ → Value τ + S τ
run i term = stepn i ($ ε term nil)

{-
test : Term ε nat
test =
  lambda _ _ (num _ 3) ▸
  call _ _ $0 ε ▸
  lambda _ _ (num _ 2) ▸
  call _ _ $0 ε ▸
  lambda (nat ∷ nat ∷ ε) _ (add _) ▸
  call _ _ $0 ($1 ∷ $3 ∷ ε) ▸
  ret $0

_ : {!!}
_ = {!run 50 test!}
-}

data IsLeft {A B : Set} : A + B → Set where
  isLeft : {a : A} → IsLeft (inl a)

data IsRight {A B : Set} : A + B → B → Set where
  isRight : {b : B} → IsRight (inr b) b

data Finishes {τ : Type} : S τ → Set where
  fin : ∀ {s : S τ} → IsLeft (step s) → Finishes s
  nex : ∀ {s} s' → IsRight (step s) s' → Finishes s' → Finishes s

{-# TERMINATING #-}
NormValue : ∀ {τ} → Value τ → Set
NormValue {ρs ⇒ τ} (#closure .ρs .τ env term) = (args : Env ρs) → All2 NormValue args → Finishes ($ (args ++' env) term nil)
NormValue {σ τs} (#inj _ τ i v) = NormValue v
NormValue {π τs} (#tuple _ vs) = All2 NormValue vs
NormValue {nat} #zero = ⊤
NormValue {nat} (#succ v) = NormValue v 

NormEnv : ∀ {Γ} → Env Γ → Set
NormEnv env = All2 (\v → NormValue v) env

NormTermCont : ∀ {Γ τ ϕ} → Term Γ τ → Cont τ ϕ → Set
NormTermCont {Γ} {τ} {ϕ} term cont =
  (env : Env Γ) → NormEnv env
  → Finishes ($ env term cont)

NormTerm : ∀ {Γ τ} → Term Γ τ → Set
NormTerm term = NormTermCont term nil

data NormCont {ρ} : ∀ {τ} → Cont ρ τ → Set where
  normNil : NormCont nil
  normCons
    : ∀ {Γ τ ϕ env term cont}
    → NormEnv {Γ} env → NormTerm {ρ ∷ Γ} {τ} term → NormCont {τ} {ϕ} cont → NormCont (cons env term cont)

lemNormTermCont : ∀ {Γ τ ϕ} term cont → NormTerm {Γ} {τ} term → NormCont {τ} {ϕ} cont → NormTermCont term cont
lemNormTermCont term nil normTermNil normCont = normTermNil
lemNormTermCont term (cons env' term' cont) normTermNil (normCons normEnv' normTerm' normCont) = {!!}

{-
$ env term nil ↝ value
NormValue value
$ env term (cons env' term' cont) →* $ (value ∷ env') term' cont
-}

{-
normTerm : ∀ {Γ τ} → (term : Term Γ τ) → NormTerm term
normTerm (ret x) env normEnv = fin isLeft
normTerm (set (lambda ρs τ termf) term) env normEnv =
  nex
    (put (#closure ρs τ env termf) env term nil)
    isRight
    ( normTerm
        term
        (#closure ρs τ env termf ∷ env)
        ( ( \args normArgs →
            normTerm termf (args ++' env) (normArgs ++2 normEnv)
          )
        ∷ normEnv
        )
    )
normTerm (set (call ρs τ f xs) term) env normEnv with get env f | get2 normEnv f
… | #closure .ρs .τ envf termf | normF = nex (let vxs = mapAll (get env) xs in fcall (vxs ++' envf) termf env term nil) {!!} (lemNormTermCont termf (cons env term nil) {!normF!} {!!} (mapAll (λ {a} → get env) xs ++' envf) {!!})
  


normTerm (set (inj τs τ x x₁) term) env normEnv = {!!}
normTerm (set (case τs ρ x x₁) term) env normEnv = {!!}
normTerm (set (tuple τs x) term) env normEnv = {!!}
normTerm (set (untuple τs ρ x x₁) term) env normEnv = {!!}
normTerm (set zero term) env normEnv = {!!}
normTerm (set (succ x) term) env normEnv = {!!}
normTerm (set (foldNat ρ x x₁ x₂) term) env normEnv = {!!}
-}
  
data NormS {τ} : S τ → Set where
  $$ : ∀ {Γ ρ env term cont} → NormEnv {Γ} env → NormTerm {Γ} {ρ} term → NormCont cont → NormS ($ env term cont)

norm : ∀ {Γ ρ τ} env term cont → NormEnv {Γ} env → NormTerm {Γ} {ρ} term → NormCont {ρ} {τ} cont → Finishes ($ env term cont)
norm = {!!}
{-
norm env (ret x) nil _ _ _ = fin isLeft
norm env (ret x) (cons env' term cont') normEnv _ normCont = nex ((put (get env x) env' term cont')) isRight (norm _ _ _ (get2 normEnv x ∷ {!normCont!}) {!!} {!!})
norm env (set (lambda ρs τ x) term) cont x₁ x₂ x₃ = nex (put (#closure ρs τ env x) env term cont) isRight (norm _ _ _ ({!!} ∷ x₁) {!x₂!} x₃)
norm env (set (call ρs τ x x₁) term) cont _ _ _ = {!!}
norm env (set (inj τs τ x x₁) term) cont _ _ _ = {!!}
norm env (set (case τs ρ x x₁) term) cont _ _ _ = {!!}
norm env (set (tuple τs x) term) cont _ _ _ = {!!}
norm env (set (untuple τs ρ x x₁) term) cont _ _ _ = {!!}
norm env (set zero term) cont _ _ _ = {!!}
norm env (set (succ x) term) cont _ _ _ = {!!}
norm env (set (foldNat ρ x x₁ x₂) term) cont _ _ _ = {!!}
-}
