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

  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  infixr 5 _⊆_
  _⊆_ : {A : Set} → (P Q : A → Set) → (A → Set)
  (P ⊆ Q) a = P a → Q a

  data _∪_ {A : Set} (P Q : A → Set) : A → Set where
    inl : ∀ {a} → P a → (P ∪ Q) a
    inr : ∀ {a} → Q a → (P ∪ Q) a

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

  reverse : {A : Set} → List A → List A
  reverse as = go as ε where
    go : {A : Set} → List A → List A → List A
    go ε cs = cs
    go (a ∷ as) cs = go as (a ∷ cs)

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

  single' : {A : Set} {P : A → Set} {a : A} → P a → All P (single a)
  single' Pa = Pa ∷ ε

  _++'_ : {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
  ε ++' Pys = Pys
  (Px ∷ Pxs) ++' Pys = Px ∷ (Pxs ++' Pys)

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get (x ∷ env) here = x
  get (x ∷ env) (there var) = get env var

  mapAll : {A : Set} {P Q : A → Set} {as : List A} → ({a : A} → P a → Q a) → All P as → All Q as
  mapAll f ε = ε
  mapAll f (Pa ∷ Pas) = f Pa ∷ mapAll f Pas

  _→[_]_ : {A : Set} → (as : List A) → (P : A → Set) → Set → Set
  ε →[ P ] R = R
  (a ∷ as) →[ P ] R = P a → (as →[ P ] R)

  applyAll : {A R : Set} {P : A → Set} {as : List A} → (Pas : All P as) → (as →[ P ] R) → R
  applyAll ε f = f
  applyAll (Pa ∷ Pas) f = applyAll Pas (f Pa)

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

  mapAny : {A : Set} {P Q : A → Set} {as : List A} → ({a : A} → P a → Q a) → Any P as → Any Q as
  mapAny f (here Pa) = here (f Pa)
  mapAny f (there Pas) = there (mapAny f Pas)

  mapAnyAll : {A R : Set} {P : A → Set} {as : List A} → Any P as → All (\a → P a → R) as → R
  mapAnyAll (here Pa) (fa ∷ fas) = fa Pa
  mapAnyAll (there Pas) (fa ∷ fas) = mapAnyAll Pas fas

  mapAllAny : {A R : Set} {P : A → Set} {as : List A} → All P as → Any (\a → P a → R) as → R
  mapAllAny (Pa ∷ Pas) (here fa)   = fa Pa
  mapAllAny (Pa ∷ Pas) (there fas) = mapAllAny Pas fas

  getAllAny : {A R : Set} {P Q : A → Set} {as : List A} → All Q as → Any P as → ({a : A} → P a → Q a → R) → R
  getAllAny (Qa ∷ Qas) (here Pa) f = f Pa Qa
  getAllAny (Qa ∷ Qas) (there anyPas) f = getAllAny Qas anyPas f

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
  #Sum : List Type → Type
  #Product : List Type → Type
  #Nat : Type
  --#List : Type → Type
  --#Conat : Type
  --#Colist : Type → Type
  #Stream : Type → Type

#Void : Type
#Void = #Sum ε

#Unit : Type
#Unit = #Product ε

#Either : Type → Type → Type
#Either σ τ = #Sum (σ ∷ τ ∷ ε)

#Pair : Type → Type → Type
#Pair σ τ = #Product (σ ∷ τ ∷ ε)

#Maybe : Type → Type
#Maybe τ = #Either #Unit τ

Var : List Type → Type → Set
Var Γ τ = Has Γ τ

module _ (%Value : Type → Set) (%Closure : List Type → Type → Set) where
  IntrF : Type → Set
  IntrF (ρs ⇒ τ)      = %Closure ρs τ
  IntrF (#Sum τs)     = Any %Value τs
  IntrF (#Product τs) = All %Value τs
  IntrF #Nat          = %Value (#Maybe #Nat)
  IntrF (#Stream τ)   = Σ Type (\ρ → %Value ρ × %Closure (single ρ) (#Pair τ ρ))

  ElimF : Type → Type → Set
  ElimF (ρs ⇒ τ)      = \ϕ → Eq τ ϕ × All %Value ρs
  ElimF (#Sum τs)     = \ϕ → All (\τ → %Closure (single τ) ϕ) τs
  ElimF (#Product τs) = \ϕ → Any (\τ → %Closure (single τ) ϕ) τs
  ElimF #Nat          = \ϕ → %Closure (single (#Maybe ϕ)) ϕ
  ElimF (#Stream τ)   = \ϕ → Eq (#Pair τ (#Stream τ)) ϕ

  module _
      (%unwrap : ∀ {τ} → %Value τ → IntrF τ)
      (%wrap : ∀ {τ} → IntrF τ → %Value τ)
      (%apply : ∀ {ρs τ} → %Closure ρs τ → All %Value ρs → %Value τ)
    where

    cut : ∀ τ {ϕ} → (%Value τ → %Value ϕ) → IntrF τ → ElimF τ ϕ → %Value ϕ
    cut (ρs ⇒ τ)      rec closure (refl , values) = %apply closure values
    cut (#Sum τs)     rec value1 closures = getAllAny closures value1 (\value closure → %apply closure (single' value))
    cut (#Product τs) rec values closure1 = getAllAny values closure1 (\closure value → %apply closure (single' value))
    cut #Nat          rec value closure =
      mapAnyAll (%unwrap value)
        ( (\value-unit → %apply closure (single' (%wrap (here value-unit))))
        ∷ (\value-nat  → %apply closure (single' (%wrap (there (here (rec value-nat))))))
        ∷ ε
      )
    cut (#Stream τ)   rec (ρ ,, value-ρ , closure) refl = applyAll (%unwrap (%apply closure (single' value-ρ))) \value-τ value'-ρ → %wrap (value-τ ∷ %wrap (ρ ,, value'-ρ , closure) ∷ ε)

  data TermF : Type → Set where
    intr : ∀ {τ} → IntrF τ → TermF τ
    elim : ∀ {τ ϕ} → ElimF τ ϕ → TermF τ → TermF ϕ

  data TermSeq (Γ : List Type) : Type → Set where
    ret : ∀ {τ} → Has Γ τ → TermSeq Γ τ
    set : ∀ {ρ τ} → TermF ρ → TermSeq (ρ ∷ Γ) τ → TermSeq Γ τ

  data TermSeq* (Γ : Type → Set) : Type → Set where
    ret : ∀ {τ} → Γ τ → TermSeq* Γ τ
    set : ∀ {ρ τ} → TermF ρ → TermSeq* (Eq ρ ∪ Γ) τ → TermSeq* Γ τ

module _ (%Closure : List Type → Type → Set) where
  data ValueF (τ : Type) : Set where
    wrap : IntrF ValueF %Closure τ → ValueF τ
    
  EnvF : List Type → Set
  EnvF τs = All ValueF τs
    
  data ExprSeq : List Type → Set where
    ε : ExprSeq ε
    _∷_ : ∀ {Γ τ} → ExprSeq Γ → TermF (Has Γ) %Closure τ → ExprSeq (τ ∷ Γ)

  data ExprSeq' (Γ : List Type) : List Type → Set where
    ε : ExprSeq' Γ ε
    _∷_ : ∀ {τs τ} → ExprSeq' Γ τs → TermF (Has (τs ++ Γ)) %Closure τ → ExprSeq' Γ (τ ∷ τs)

mutual
  Expr : List Type → Type → Set
  Expr Γ τ = TermF (\ϕ → Has Γ ϕ) (\ρs ϕ → Term (ρs ++ Γ) ϕ) τ
  
  data Term (Γ : List Type) : Type → Set where
    ret : ∀ {τ} → Has Γ τ → Term Γ τ 
    set : ∀ {ρ ϕ} → Expr Γ ρ → Term (ρ ∷ Γ) ϕ → Term Γ ϕ
    --set : ∀ {ϕ} → TermF (\τ → Term Γ τ) (\ρs τ → Term (ρs ++ Γ) τ) ϕ → Term Γ ϕ

data TermP* (Γ : Type → Set) (τ : Type) : Set where
  pure : Γ τ → TermP* Γ τ
  roll : TermF (\ϕ → TermP* Γ ϕ) (\ρs ϕ → TermP* (\σ → Has ρs σ + Γ σ) ϕ) τ → TermP* Γ τ

data TermP (Γ : List Type) (τ : Type) : Set where
  pure : Has Γ τ → TermP Γ τ
  roll : TermF (\ϕ → TermP Γ ϕ) (\ρs ϕ → TermP (ρs ++ Γ) ϕ) τ → TermP Γ τ

data PrettyTerm (Γ : List Type) (ϕ : Type) : Set where
  wrap : TermF (\τ → PrettyTerm Γ τ) (\ρs τ → PrettyTerm (ρs ++ Γ) τ) ϕ → PrettyTerm Γ ϕ
  --lett : ∀ {ρ} → PrettyTerm Γ ρ → PrettyTerm (ρ ∷ Γ) ϕ → PrettyTerm Γ ϕ

mutual
  data Value (τ : Type) : Set where
    wrap : IntrF Value Closure τ → Value τ

  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {τs} → Env τs → Term (ρs ++ τs) τ → Closure ρs τ

  Env : List Type → Set
  Env τs = All Value τs

mutual
  data Value' (τ : Type) : Set where
    wrap : IntrF Value' Closure' τ → Value' τ

  data Closure' (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {τs} → Env' τs → TermP (ρs ++ τs) τ → Closure' ρs τ

  Env' : List Type → Set
  Env' τs = All Value' τs

eval : ∀ {Γ τ} → TermP Γ τ → All Value' Γ → Value' τ
eval (pure x) env = get env x
eval (roll (intr {ρs ⇒ τ} f)) env = wrap {!!}
eval (roll (intr {#Sum τs} t1)) env = {!wrap (mapAny (\t → eval t env) t1)!}
eval (roll (intr {#Product τs} ts)) env = {!wrap (mapAll (\t → eval t env) ts)!}
eval (roll (intr {#Nat} x)) env = {!eval x env!}
eval (roll (intr {#Stream τ} (ρ ,, v , t))) env = wrap (ρ ,, eval v env , {!!})
eval (roll (elim {τ} x term)) env = {!!}

--data CallStack : List Type → Type → Set where
--  ε   : ∀ {τ} → CallStack (single τ) τ
--  _∷_ : ∀ {ρs τ ϕ} → Closure ρs τ → CallStack (single τ) ϕ → CallStack ρs ϕ
data Comp : List Type → Type → Set where
  val : ∀ {τ} → Value τ → Comp ε τ
  ε   : ∀ {τ} → Comp (single τ) τ
  _∷_ : ∀ {ρs τ ϕ} → Comp ρs τ → Comp (single τ) ϕ → Comp ρs ϕ

applyClosure : ∀ {ρs τ} → Closure ρs τ → Env ρs → Closure ε τ
applyClosure (env & term) values = (values ++' env) & term

stepAll : {T : Set} {τs : List T} {P Q : T → Set} → All (\τ → (Q ⊆ P ∪ Q) τ) τs → All (P ∪ Q) τs → All (P ∪ Q) τs
stepAll step-τs ε = ε
stepAll (step-τ ∷ step-τs) (inl Pτ ∷ PQτs) = inl Pτ ∷ stepAll step-τs PQτs
stepAll (step-τ ∷ step-τs) (inr Qτ ∷ PQτs) = step-τ Qτ ∷ PQτs

stepExprF : ∀ {τ} → TermF Value Closure τ → Comp ε τ
stepExprF = {!!}

{-
applicative
- f a → f b → f (a × b)
- () → f ()

- TermF %Value1 %Closure1 → 
-
-}
module _
    {%Value1 %Value2 : Type → Set}
    (mapValue : ∀ {τ} → %Value1 τ → %Value2 τ)
    (%Closure1 %Closure2 : List Type → Type → Set)
    (mapClosure : ∀ {ρs τ} → %Closure1 ρs τ → %Closure2 ρs τ)
  where

  mapTermF : ∀ {τ} → TermF %Value1 %Closure1 τ → TermF %Value2 %Closure2 τ
  mapTermF = {!!}
  {-
  mapTermF (lambda f)        = lambda (mapClosure f)
  mapTermF (call f xs)       = call (mapValue f) (mapAll mapValue xs)
  mapTermF (inj x)           = inj (mapAny mapValue x)
  mapTermF (case x ts)       = case (mapValue x) (mapAll mapClosure ts)
  mapTermF (tuple xs)        = tuple (mapAll mapValue xs)
  mapTermF (untuple x t)     = untuple (mapValue x) (mapClosure t)
  mapTermF (buildNat f)      = buildNat (mapValue f)
  mapTermF (foldNat x f)     = foldNat (mapValue x) (mapClosure f)
  mapTermF (buildList f)     = buildList (mapValue f)
  mapTermF (foldList x f)    = foldList (mapValue x) (mapClosure f)
  mapTermF (buildConat x f)  = buildConat (mapValue x) (mapClosure f)
  mapTermF (forceConat x)    = forceConat (mapValue x)
  mapTermF (buildColist x f) = buildColist (mapValue x) (mapClosure f)
  mapTermF (forceColist x)   = forceColist (mapValue x)
  mapTermF (buildStream x f) = buildStream (mapValue x) (mapClosure f)
  mapTermF (forceStream x)   = forceStream (mapValue x)
  -}

{-
Term Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ

All (Term Γ) ρs → Term (ρs ++ Γ) ϕ → Term Γ ϕ

-}

stepExpr : ∀ {ρs τ} → Env ρs → Expr ρs τ → Comp ε τ
stepExpr = {!!}

composeComp : ∀ {ρs τ ϕ} → Comp ρs τ → Comp (single τ) ϕ → Comp ρs ϕ
composeComp (val v) stack2 = {!!}
composeComp ε stack2 = stack2
composeComp (closure ∷ stack1) stack2 = closure ∷ composeComp stack1 stack2

step : ∀ {τ} → Comp ε τ → Comp ε τ
step = {!!}
