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

  data TermF : Type → Set where
    intr : ∀ {τ} → IntrF τ → TermF τ
    elim : ∀ {τ ϕ} → TermF τ → ElimF τ ϕ → TermF ϕ

  module _ (&Value : ∀ {τ} → %Value τ → Set) (&Closure : ∀ {ρs τ} → %Closure ρs τ → Set) where
    AllIntrF : ∀ τ → IntrF τ → Set
    AllIntrF (ρs ⇒ τ) closure = &Closure closure
    AllIntrF (#Sum τs) any-value = {!!}
    AllIntrF (#Product τs) values = {!!}
    AllIntrF #Nat value = &Value value 
    AllIntrF (#Stream τ) (ρ ,, value , closure) = &Value value × &Closure closure

    AllElimF : ∀ {ϕ} τ → ElimF τ ϕ → Set
    AllElimF τ eli = {!!}

    AllTermF : ∀ {τ} → TermF τ → Set
    AllTermF = {!!}

module _ (%Term : List Type → Type → Set) where
  mutual
    data ValueF (τ : Type) : Set where
      wrap : IntrF ValueF %Term τ → ValueF τ

    data ClosureF (ρs : List Type) (τ : Type) : Set where
      _&_ : ∀ {τs} → All ValueF τs → %Term (ρs ++ τs) τ → ClosureF ρs τ

  data AllValueF (&Term : ∀ {ρs τ} → %Term ρs τ → Set) {τ} : ValueF τ → Set where
    wrapAllValueF : ∀ {valueU : IntrF ValueF %Term τ} → AllIntrF ValueF %Term (\_ → ⊤) &Term τ valueU → AllValueF &Term (wrap valueU)

mutual
  TermU : List Type → Type → Set
  TermU Γ ϕ = TermF (\τ → Term Γ τ) (\ρs τ → Term (ρs ++ Γ) τ) ϕ

  data Term (Γ : List Type) (ϕ : Type) : Set where
    wrap : TermU Γ ϕ → Term Γ ϕ

-- compile
module _ where
  mutual
    Expr : List Type → Type → Set
    Expr Γ τ = TermF (Has Γ) (\ϕs ϕ → TermM ϕs ϕ) τ
  
    data TermM (Γ : List Type) : Type → Set where
      ret : ∀ {τ} → Has Γ τ → TermM Γ τ
      set : ∀ {ρ τ} → Expr Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  
  Value : Type → Set
  Value = ValueF TermM
  
  Closure : List Type → Type → Set
  Closure = ClosureF TermM

  Env : List Type → Set
  Env τs = All Value τs
  
  data CallStack : List Type → Type → Set where
    ε : ∀ {τ} → CallStack (single τ) τ
    _∷_ : ∀ {ρs σ τ} → Closure ρs σ → CallStack (single σ) τ → CallStack ρs τ
  
  Machine : Type → Set
  Machine τ = CallStack ε τ

  sequentialize : ∀ {Γ τ} → Term Γ τ → TermM Γ τ
  sequentialize expr = {!!}

  compile : ∀ {τ} → Term ε τ → Machine τ
  compile term = (ε & sequentialize term) ∷ ε

module _ where
  data Step (τ : Type) : Set where
    finish : Value τ → Step τ
    continue : Machine τ → Step τ

  composeValueClosure : ∀ {σ τ} → Value σ → Closure (single σ) τ → Closure ε τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  composeValueStack : ∀ {σ τ} → Value σ → CallStack (single σ) τ → Step τ
  composeValueStack value ε = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)

  composeStackStack : ∀ {ρs σ τ} → CallStack ρs σ → CallStack (single σ) τ → CallStack ρs τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeStepStack : ∀ {ρ τ} → Step ρ → CallStack (single ρ) τ → Step τ
  composeStepStack (finish value) stack = composeValueStack value stack
  composeStepStack (continue stack') stack = continue (composeStackStack stack' stack)

  stepExpr : ∀ {ρs τ} → Env ρs → Expr ρs τ → Step τ
  stepExpr env expr = {!expr!}

  stepClosure : ∀ {τ} → Closure ε τ → Step τ
  stepClosure (env & ret x) = finish (get env x)
  stepClosure (env & set expr term) = composeStepStack (stepExpr env expr) ((env & term) ∷ ε)

  step : ∀ {τ} → Machine τ → Step τ
  step (closure ∷ stack) = composeStepStack (stepClosure closure) stack

-- composeStepStack (step machine) cont ≡ step (composeStackStack machine cont)
module _ where
  eq-composeStepStack :
    ∀ {σ τ} (machine : Machine σ) (stack : CallStack (single σ) τ)
    → composeStepStack (step machine) stack ≡ step (composeStackStack machine stack)
  eq-composeStepStack = {!!}

