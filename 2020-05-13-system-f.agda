module _ where

module _ where
  data ⊥ : Set where
  
  record ⊤ : Set where
    constructor tt

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  infixr 15 _×_
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

  infixr 10 _+_
  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  data Eq {A : Set} (a : A) : A → Set where
    refl : Eq a a

  _≡_ = Eq

  data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (succ n)
    succ : ∀ {n} → Fin n → Fin (succ n)

  data Vector (A : Set) : ℕ → Set where
    ε : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

  Has : {A : Set} → List A → A → Set
  Has as a = Any (Eq a) as

  transport : {A : Set} → (P : A → Set) → ∀ {a a'} → a ≡ a' → P a → P a'
  transport P refl Pa = Pa

  cong : {A B : Set} → (f : A → B) → ∀ {a a'} → a ≡ a' → f a ≡ f a'
  cong f refl = refl

  single : ∀ {A} → A → List A
  single a = a ∷ ε

  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  $0 : ∀ {A a0 as}                      → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as}                   → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as}                → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as}             → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $4 : ∀ {A a0 a1 a2 a3 a4 as}          → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ as) a4
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2
  $4 = there $3

  single' : {A : Set} {P : A → Set} {a : A} → P a → All P (single a)
  single' Pa = Pa ∷ ε

  _++'_ : {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
  ε ++' Pys = Pys
  (Px ∷ Pxs) ++' Pys = Px ∷ (Pxs ++' Pys)

  mapList : {A B : Set} → (A → B) → (List A → List B)
  mapList f ε = ε
  mapList f (a ∷ as) = f a ∷ mapList f as

  mapAll : {A : Set} {P Q : A → Set} → (∀ {a} → P a → Q a) → (∀ {as} → All P as → All Q as)
  mapAll f ε = ε
  mapAll f (Pa ∷ Pas) = f Pa ∷ mapAll f Pas

  mapAny : {A : Set} {P Q : A → Set} → (∀ {a} → P a → Q a) → (∀ {as} → Any P as → Any Q as)
  mapAny f (here Pa) = here (f Pa)
  mapAny f (there Pas) = there (mapAny f Pas)

  zipAllAny : {A R : Set} {P Q : A → Set} → ∀ {as} → All P as → Any Q as → (∀ {a} → P a → Q a → R) → R
  zipAllAny (Pa ∷ Pas) (here Qa) f = f Pa Qa
  zipAllAny (Pa ∷ Pas) (there any-Q) f = zipAllAny Pas any-Q f

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get all-p any-eq = zipAllAny all-p any-eq (\{ Pa refl → Pa })

module _ where
  infixr 5 _⇒_
  data Type (n : ℕ) : Set where
    #Var     : Fin n → Type n
    _⇒_      : Type n → Type n → Type n
    #Sum     : List (Type n) → Type n
    #Product : List (Type n) → Type n
    #Nat     : Type n
    #Forall  : Type (succ n) → Type n
    #Exists  : Type (succ n) → Type n

  #Void : ∀ {n} → Type n
  #Void = #Sum ε
  
  #Unit : ∀ {n} → Type n
  #Unit = #Product ε
  
  #Either : ∀ {n} → Type n → Type n → Type n
  #Either σ τ = #Sum (σ ∷ τ ∷ ε)
  
  #Pair : ∀ {n} → Type n → Type n → Type n
  #Pair σ τ = #Product (σ ∷ τ ∷ ε)

  #Bool : ∀ {n} → Type n
  #Bool = #Either #Unit #Unit
  
  #Maybe : ∀ {n} → Type n → Type n
  #Maybe τ = #Either #Unit τ

-- context
module _ where
  data Ctx : ℕ → Set where
    ε : Ctx zero
    ∗∷_ : ∀ {n} → Ctx n → Ctx (succ n)
    _∷_ : ∀ {n} → Type n → Ctx n → Ctx n

{-
∀α.α→α

Type0 : Set
- _⇒_   : Type0 → Type0 → Type0
- Maybe : Type0 → Type0
- ℕ     : Type0
- ∀ ∃   : Type1 → Type0
- _#_   : Type1 → Type0 → Type0

Type1 : Set
- α₀   : Type1
- _⇒₁_ : Type1 → Type1 → Type1
- Maybe₁ : Type1 → Type1
- ℕ₁   : Type1

↑ᶜ : List Type0 → List Type1

Term : List Type0 → Type0 → Set
- var    : Has Γ τ → Term Γ τ
- ⇒-intr : Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
- ⇒-elim : Term Γ σ → Term Γ (σ ⇒ τ) → Term Γ τ
- Maybe-intr : ⊤ + Term Γ τ → Term Γ (Maybe τ)
- Maybe-elim : Term Γ ϕ → Term Γ (τ ⇒ ϕ) → Term Γ (Maybe τ) → Term Γ ϕ
- ℕ-intr : Term Γ (Maybe ℕ) → Term Γ ℕ
- ℕ-elim : Term Γ (Maybe ϕ ⇒ ϕ) → Term Γ ℕ → Term Γ ϕ
- ∀-intr : Term₁ (↑ᶜ Γ) τ₁ → Term Γ (∀ τ₁)
- ∀-elim : ∀ ϕ₀ → Term Γ (∀ τ₁) → Term Γ (τ₁ # ϕ₀)
- ∃-intr : ∀ σ₀ → Term Γ (τ₁ # σ₀) → Term Γ (∃ τ₁)
- ∃-elim : ∀ ϕ₀ → Term Γ (∃ τ₁) → Term₁ (↑ᶜ Γ) (τ₁ ⇒₁ ↑ᵗ ϕ₀) → Term Γ ϕ₀

Term₁ : List Type1 → Type1 → Set
- var₁    : Has Γ τ₁ → Trem Γ τ₁
- ⇒-intr₁ : Term₁ (σ ∷ Γ) τ → Term₁ Γ (σ ⇒₁ τ)
- ⇒-elim₁ : Term₁ Γ σ → Term₁ Γ (σ ⇒ τ) → Term₁ Γ τ
- ℕ-intr₁ : Term₁ Γ (Maybe ℕ₁) → Term₁ Γ ℕ₁
- ℕ-elim₁ : Term₁ Γ (Maybe ϕ ⇒ ϕ) → Term₁ Γ ℕ₁ → Term₁ Γ ϕ

Value : Type0 → Set
- ⇒-intr : Env Γ → Term (σ ∷ Γ) τ → Value (σ ⇒ τ)
- ℕ-intr : Value Γ (Maybe ℕ) → Term Γ ℕ
- ∀-intr : Env Γ → Term₁ (↑ᶜ Γ) τ₁ → Value (∀ τ₁)
- ∃-intr : ∀ σ₀ → Value (τ₁ # σ₀) → Value (∃ τ₁)

Thunk τ = (Γ : _) × Env Γ × Term Γ τ

eliminate : Value τ → ElimR τ ϕ → Thunk ϕ

-}

-- intr, elim
module _ where
  {-# TERMINATING #-}
  _#_ : ∀ {n} → Type (succ n) → Type n → Type n
  _#_ = {!!}

  {-# TERMINATING #-}
  ↑ᵗ_ : ∀ {n} → Type n → Type (succ n)
  ↑ᵗ #Var x = #Var (succ x)
  ↑ᵗ (τ ⇒ τ₁) = ↑ᵗ τ ⇒ ↑ᵗ τ₁
  ↑ᵗ #Sum x = #Sum (mapList ↑ᵗ_ x)
  ↑ᵗ #Product x = {!!}
  ↑ᵗ #Nat = {!!}
  ↑ᵗ #Forall τ = {!!}
  ↑ᵗ #Exists τ = {!!}

  data Intr (n : ℕ) (%AbsType : Type (succ n) → Set) (%Function : Type n → Type n → Set) (%Value : Type n → Set) : Type n → Set where
    intrArrow   : ∀ {ρ τ}  → %Function ρ τ                                   → Intr n %AbsType %Function %Value (ρ ⇒ τ)
    intrSum     : ∀ {τs}   → Any %Value τs                                   → Intr n %AbsType %Function %Value (#Sum τs)
    intrProduct : ∀ {τs}   → All %Value τs                                   → Intr n %AbsType %Function %Value (#Product τs)
    intrNat     :            %Value (#Maybe #Nat)                            → Intr n %AbsType %Function %Value  #Nat
    intrForall  : (τ⁺ : Type (succ n)) → %AbsType τ⁺ → Intr n %AbsType %Function %Value (#Forall τ⁺)
    intrExists  : (τ⁺ : Type (succ n)) → (ϕ : Type n) → %Value (τ⁺ # ϕ) → Intr n %AbsType %Function %Value (#Exists τ⁺)
  
  data Elim (n : ℕ) (%AbsType : Type (succ n) → Set) (%Value : Type n → Set) : Type n → Type n → Set where
    elimArrow   : ∀ {ρ τ}  → %Value ρ                                        → Elim n %AbsType %Value (ρ ⇒ τ)       τ
    elimSum     : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs                    → Elim n %AbsType %Value (#Sum τs)     ϕ
    elimProduct : ∀ {τs τ} → Has τs τ                                        → Elim n %AbsType %Value (#Product τs) τ
    elimNat     : ∀ {ϕ}    → %Value (#Maybe ϕ ⇒ ϕ)                           → Elim n %AbsType %Value  #Nat         ϕ
    elimForall  : (τ⁺ : Type (succ n)) → (ϕ : Type n) → Elim n %AbsType %Value (#Forall τ⁺) (τ⁺ # ϕ)
    elimExists  : (τ⁺ : Type (succ n)) → (ϕ : Type n) → %AbsType (τ⁺ ⇒ ↑ᵗ ϕ) → Elim n %AbsType %Value (#Exists τ⁺) ϕ
  
  data ExprF (n : ℕ) (%AT : Type (succ n) → Set) (%F : Type n → Type n → Set) (%V : Type n → Set) (τ : Type n) : Set where
    intr : Intr n %AT %F %V τ               → ExprF n %AT %F %V τ
    elim : ∀ {ϕ} → %V ϕ → Elim n %AT %V ϕ τ → ExprF n %AT %F %V τ

module _ where
  Var : ∀ {n} → Ctx n → Type n → Set
  Var = {!!}

  mutual
    -- regular de-bruijn term
    data Term (n : ℕ) (Γ : Ctx n) (τ : Type n) : Set where
      var  : Var Γ τ → Term n Γ τ
      wrap : ExprF n (TermAbsT n Γ) (TermAbs n Γ) (Term n Γ) τ → Term n Γ τ
  
    TermAbs : (n : ℕ) → Ctx n → (Type n → Type n → Set)
    TermAbs n Γ ρ τ = Term n (ρ ∷ Γ) τ

    TermAbsT : (n : ℕ) → Ctx n → (Type (succ n) → Set)
    TermAbsT n Γ τ⁺ = Term (succ n) (∗∷ Γ) τ⁺

example : Term 1 (#Var zero ∷ ∗∷ ε) (#Forall (#Var zero ⇒ #Var (succ zero)))
example = wrap (intr (intrForall (#Var zero ⇒ #Var (succ zero)) (wrap (intr (intrArrow (var $1))))))


-- compiled representation
module _ where
  infixr 5 _▸_
  mutual
    data TermM (n : ℕ) (Γ : List (Type n)) (τ : Type n) : Set where
      return : Has Γ τ → TermM n Γ τ
      _▸_    : ∀ {ρ} → ExprF n (AbsTermMT n Γ) (AbsTermM n Γ) (Has Γ) ρ → TermM n (ρ ∷ Γ) τ → TermM n Γ τ

    AbsTermM : (n : ℕ) → List (Type n) → (Type n → Type n → Set)
    AbsTermM n Γ σ τ = TermM n (σ ∷ Γ) τ

    AbsTermMT : (n : ℕ) → List (Type n) → (Type (succ n) → Set)
    AbsTermMT n Γ τ = TermM (succ n) (mapList ↑ᵗ_ Γ) τ
{-
  IntrM : List Type → Type → Set
  IntrM Γ τ = Intr (AbsTermM Γ) (Has Γ) τ

  ElimM : List Type → Type → Type → Set
  ElimM Γ τ ϕ = Elim (Has Γ) τ ϕ
  -}

  ExprM : (n : ℕ) → List (Type n) → Type n → Set
  ExprM n Γ τ = ExprF n (AbsTermMT n Γ) (AbsTermM n Γ) (Has Γ) τ

  pure : ∀ {n Γ τ} → ExprM n Γ τ → TermM n Γ τ
  pure expr = expr ▸ return $0

{-
-- run-time representation
module _ where
  _##_ : ∀ {n} → List (Type n) → Vector (Type 0) n → List (Type 0)
  _##_ = ?

  _#*_ : ∀ {n} → Type n → Vector (Type 0) n → Type 0
  _#*_ = ?

{-
  mutual
    data Value (τ : Type 0) : Set where
      construct : Intr 0 ClosureT Closure Value τ → Value τ

    data Closure (ρ : Type 0) : (τ : Type 0) → Set where
      _&_ : ∀ {n} → {τ' : Type n} {Γ : List (Type n)}
          → (τs : Vector (Type 0) n) → Env (Γ ## τs) → TermM n (? ∷ Γ) τ' → Closure ρ (τ' #* τs)

    data ClosureT (τ : Type 1) : Set where
      _&_ : ∀ {n Γ} → Vector (Type 0) n → Env Γ → TermM (succ n) Γ τ → ClosureT τ

    Env : List (Type 0) → Set
    Env Γ = All Value Γ
    -}

  {-
  IntrR : Type → Set
  IntrR τ = Intr Closure Value τ

  ElimR : Type → Type → Set
  ElimR τ ϕ = Elim Value τ ϕ

  unwrapValue : ∀ {τ} → Value τ → Intr Closure Value τ
  unwrapValue (construct rule) = rule
  -}

  data Thunk (τ : Type zero) : Set where
    _&_ : ∀ {Γ} → Env zero Γ → TermM zero Γ τ → Thunk τ

  data CallStack : Type zero → Type zero → Set where
    ε   : ∀ {τ} → CallStack τ τ
    _∷_ : ∀ {ρ σ τ} → Closure zero ρ σ → CallStack σ τ → CallStack ρ τ

  data Machine : Type zero → Set where
    _∷_ : ∀ {σ τ} → Thunk σ → CallStack σ τ → Machine τ

  data Step (τ : Type zero) : Set where
    finish   : Value zero τ → Step τ
    continue : Machine τ → Step τ

  composeValueClosure : ∀ {σ τ} → Value 0 σ → Closure 0 σ τ → Thunk τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  composeStackStack : ∀ {ρ σ τ} → CallStack ρ σ → CallStack σ τ → CallStack ρ τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeMachineStack : ∀ {σ τ} → Machine σ → CallStack σ τ → Machine τ
  composeMachineStack (thunk ∷ stack1) stack2 = thunk ∷ composeStackStack stack1 stack2

  composeValueStack : ∀ {σ τ} → Value 0 σ → CallStack σ τ → Step τ
  composeValueStack value ε = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)

  composeStepStack : ∀ {σ τ} → Step σ → CallStack σ τ → Step τ
  composeStepStack (finish value) stack = composeValueStack value stack
  composeStepStack (continue machine) stack = continue (composeMachineStack machine stack)

  load : ∀ {τ} → TermM 0 ε τ → Machine τ
  load term = (ε & term) ∷ ε

module _ where
  compile : ∀ {n Γ τ} → Term n Γ τ → TermM n Γ τ
  compile = {!!}

  &apply : ∀ {n Γ σ τ} → Term n Γ (σ ⇒ τ) → Term n Γ σ → Term n Γ τ
  &apply f a = wrap (elim f (elimArrow a))
  

-- elimination
module _ where
  eliminateArrow : ∀ {ρ τ ϕ} → Elim 0 (Value _) (Value _) (ρ ⇒ τ) ϕ → Value 0 (ρ ⇒ τ) → Thunk ϕ
  eliminateArrow (elimArrow value) (construct (intrArrow closure)) = composeValueClosure value closure

  eliminateSum : ∀ {τs ϕ} → Elim 0 (Value _) (Value _) (#Sum τs) ϕ → Value 0 (#Sum τs) → Thunk ϕ
  eliminateSum (elimSum fs) (construct (intrSum vᵢ)) = zipAllAny fs vᵢ (\f v → (f ∷ v ∷ ε) & compile (&apply (var $0) (var $1)))

  eliminateProduct : ∀ {τs ϕ} → Elim 0 (Value _) (Value _) (#Product τs) ϕ → Value 0 (#Product τs) → Thunk ϕ
  eliminateProduct (elimProduct i) (construct (intrProduct vs)) = (get vs i ∷ ε) & compile (var $0)

  eliminateNat : ∀ {ϕ} → Elim 0 (Value _) (Value _) #Nat ϕ → Value 0 #Nat → Thunk ϕ
  eliminateNat (elimNat s) (construct (intrNat v)) =
    (v ∷ s ∷ ε) &
    ( intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
    ▸ intr (intrArrow (elim $0 (elimNat $3) ▸ pure (intr (intrSum (there (here $0))))))
    ▸ elim $2 (elimSum ($1 ∷ $0 ∷ ε))
    ▸ pure (elim $4 (elimArrow $0))
    )

  eliminateForall : ∀ {τ⁺ ϕ} → Elim 0 (Value _) (Value _) (#Forall τ⁺) ϕ → Value 0 (#Forall τ⁺) → Thunk ϕ
  eliminateForall (elimForall ._ ._) (construct (intrForall ._ abs)) = {!!}

  eliminate : ∀ {τ ϕ} → Elim 0 (Value _) (Value _) τ ϕ → Value 0 τ → Thunk ϕ
  eliminate {ρ ⇒ τ}       = eliminateArrow
  eliminate {#Sum τs}     = eliminateSum
  eliminate {#Product τs} = eliminateProduct
  eliminate {#Nat}        = eliminateNat
  eliminate {#Forall τ⁺}  = {!!}
  eliminate {#Exists τ⁺}  = {!!}

-- computation step
module _ where
  plugEnvIntr : ∀ {Γ τ} → Env 0 Γ → Intr 0 (AbsTermMT 0 Γ) (AbsTermM 0 Γ) (Has Γ) τ → Intr 0 (Value _) (Closure 0) (Value _) τ
  --plugEnvIntr env rule = mapIntr (\term → env & term) (\x → get env x) rule
  plugEnvIntr env rule = {!!}

  plugEnvElim : ∀ {Γ τ ϕ} → Env 0 Γ → Elim 0 (AbsTermMT _ Γ) (Has Γ) τ ϕ → Elim 0 (Value _) (Value _) τ ϕ
  --plugEnvElim env rule = mapElim (\x → get env x) rule
  plugEnvElim env rule = {!!}

  reduce : ∀ {τ} → Machine τ → Step τ
  reduce ((env & return x) ∷ stack) = composeValueStack (get env x) stack
  reduce ((env & (intr rule ▸ cont)) ∷ stack) = continue (((value ∷ env) & cont) ∷ stack)
    where
      value : Value 0 _
      value = construct (plugEnvIntr env rule)
  reduce ((env & (elim x rule ▸ cont)) ∷ stack) = continue ((thunk ∷ (env & cont) ∷ stack))
    where
      thunk : Thunk _
      thunk = eliminate (plugEnvElim env rule) (get env x)
      -}
