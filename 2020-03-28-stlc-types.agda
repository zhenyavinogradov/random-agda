module _ where

module _ where
  data ⊥ : Set where
  
  record ⊤ : Set where
    constructor tt

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

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

  data All₁ {A : Set} (P : A → Set₁) : List A → Set₁ where
    ε : All₁ P ε
    _∷_ : ∀ {a as} → P a → All₁ P as → All₁ P (a ∷ as)

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

  IsAny : {A : Set} {P : A → Set} → (P2 : {a : A} → P a → Set) → {as : List A} → Any P as → Set
  IsAny P2 (here Pa) = P2 Pa
  IsAny P2 (there any-Pa) = IsAny P2 any-Pa

  mapAny : {A : Set} {P Q : A → Set} {as : List A} → ({a : A} → P a → Q a) → Any P as → Any Q as
  mapAny f (here Pa) = here (f Pa)
  mapAny f (there Pas) = there (mapAny f Pas)

  mapAnyAll : {A R : Set} {P : A → Set} {as : List A} → Any P as → All (\a → P a → R) as → R
  mapAnyAll (here Pa) (fa ∷ fas) = fa Pa
  mapAnyAll (there Pas) (fa ∷ fas) = mapAnyAll Pas fas

  mapAllAny : {A R : Set} {P : A → Set} {as : List A} → All P as → Any (\a → P a → R) as → R
  mapAllAny (Pa ∷ Pas) (here fa)   = fa Pa
  mapAllAny (Pa ∷ Pas) (there fas) = mapAllAny Pas fas

  getAllAny : {A R : Set} {P Q : A → Set} {as : List A} → All P as → Any Q as → ({a : A} → P a → Q a → R) → R
  getAllAny (Pa ∷ Pas) (here Qa) f = f Pa Qa
  getAllAny (Pa ∷ Pas) (there anyQas) f = getAllAny Pas anyQas f

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

  mapΣc : {A : Set} {B1 B2 : A → Set} → ({a : A} → B1 a → B2 a) → Σ A B1 → Σ A B2
  mapΣc f (a ,, b) = (a ,, f b)

  bimap× : {A1 B1 A2 B2 : Set} → (A1 → A2) → (B1 → B2) → A1 × B1 → A2 × B2
  bimap× f g (a , b) = f a , g b

  identity : {A : Set} → A → A
  identity a = a

-- types
module _ where
  data Type : Set where
    _⇒_ : List Type → Type → Type
    #Sum : List Type → Type
    #Product : List Type → Type
    #Nat : Type
    #List : Type → Type
    #Tree : Type → Type
    #Conat : Type
    --#Delay : Type → Type
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

  #Bool : Type
  #Bool = #Either #Unit #Unit
  
  #Maybe : Type → Type
  #Maybe τ = #Either #Unit τ

module _ (%Value : Type → Set) (%Closure : List Type → Type → Set) where
  IntrF : Type → Set
  IntrF (ρs ⇒ τ)      = %Closure ρs τ
  IntrF (#Sum τs)     = Any %Value τs
  IntrF (#Product τs) = All %Value τs
  IntrF #Nat          = %Value (#Maybe #Nat)
  IntrF (#List τ)     = %Value (#Maybe (#Pair τ (#List τ)))
  IntrF (#Tree τ)     = %Value (#Either τ (#Pair τ (#Pair (#Tree τ) (#Tree τ))))
  IntrF #Conat        = Σ Type (\ρ → %Value ρ × %Closure (single ρ) (#Maybe ρ))
  IntrF (#Stream τ)   = Σ Type (\ρ → %Value ρ × %Closure (single ρ) (#Pair τ ρ))

  ElimF : Type → Type → Set
  ElimF (ρs ⇒ τ)      = \ϕ → Eq τ ϕ × All %Value ρs
  ElimF (#Sum τs)     = \ϕ → All (\τ → %Closure (single τ) ϕ) τs
  ElimF (#Product τs) = \ϕ → Any (\τ → %Closure (single τ) ϕ) τs
  ElimF #Nat          = \ϕ → %Closure (single (#Maybe ϕ)) ϕ
  ElimF (#List τ)     = \ϕ → %Closure (single (#Maybe (#Pair τ ϕ))) ϕ
  ElimF (#Tree τ)     = \ϕ → %Closure (single (#Either τ (#Pair τ (#Pair ϕ ϕ)))) ϕ
  ElimF #Conat        = \ϕ → Eq (#Maybe #Conat) ϕ
  --ElimF #Conat      = \ϕ → %Closure (single (#Maybe #Conat)) ϕ
  ElimF (#Stream τ)   = \ϕ → Eq (#Pair τ (#Stream τ)) ϕ

  data TermF : Type → Set where
    intr : ∀ {τ} → IntrF τ → TermF τ
    elim : ∀ {τ ϕ} → %Value τ → ElimF τ ϕ → TermF ϕ

  {-
  module _ (&Value : ∀ {τ} → %Value τ → Set) (&Closure : ∀ {ρs τ} → %Closure ρs τ → Set) where
    AllIntrF : ∀ τ → IntrF τ → Set
    AllIntrF (ρs ⇒ τ) closure = &Closure closure
    AllIntrF (#Sum τs) any-value = IsAny &Value any-value
    AllIntrF (#Product τs) values = All2 &Value values
    AllIntrF #Nat value = &Value value 
    AllIntrF (#List τ) value = &Value value 
    AllIntrF #Conat (ρ ,, value , closure) = &Value value × &Closure closure
    AllIntrF (#Stream τ) (ρ ,, value , closure) = &Value value × &Closure closure
    AllIntrF _ = {!!}

    {-
    AllElimF : ∀ {ϕ} τ → ElimF τ ϕ → Set
    AllElimF τ eli = {!!}

    AllTermF : ∀ {τ} → TermF τ → Set
    AllTermF = {!!}
    -}
    -}

module _
    {%V1 %V2 : Type → Set}
    {%C1 %C2 : List Type → Type → Set}
    (%mapValue : ∀ {τ} → %V1 τ → %V2 τ)
    (%mapClosure : ∀ {ρs τ} → %C1 ρs τ → %C2 ρs τ)
  where

  mapIntrF : ∀ {τ} → IntrF %V1 %C1 τ → IntrF %V2 %C2 τ
  mapIntrF {ρs ⇒ τ}      = %mapClosure
  mapIntrF {#Sum τs}     = mapAny %mapValue
  mapIntrF {#Product τs} = mapAll %mapValue
  mapIntrF {#Nat}        = %mapValue
  mapIntrF {#List τ}     = %mapValue
  mapIntrF {#Tree τ}     = %mapValue
  mapIntrF {#Conat}      = mapΣc (bimap× %mapValue %mapClosure)
  mapIntrF {#Stream τ}   = mapΣc (bimap× %mapValue %mapClosure)

  mapElimF : ∀ {τ ϕ} → ElimF %V1 %C1 τ ϕ → ElimF %V2 %C2 τ ϕ
  mapElimF {ρs ⇒ τ}      {ϕ} = bimap× identity (mapAll %mapValue)
  mapElimF {#Sum τs}     {ϕ} = mapAll %mapClosure
  mapElimF {#Product τs} {ϕ} = mapAny %mapClosure 
  mapElimF {#Nat}        {ϕ} = %mapClosure
  mapElimF {#List τ}     {ϕ} = %mapClosure
  mapElimF {#Tree τ}     {ϕ} = %mapClosure
  mapElimF {#Conat}      {ϕ} = identity
  mapElimF {#Stream τ}   {ϕ} = identity

-- regular de bruijn term
mutual
  TermU : List Type → Type → Set
  TermU Γ ϕ = TermF (\τ → Term Γ τ) (\ρs τ → Term (ρs ++ Γ) τ) ϕ

  data Term (Γ : List Type) (ϕ : Type) : Set where
    var : Has Γ ϕ → Term Γ ϕ
    wrap : TermU Γ ϕ → Term Γ ϕ

-- compiled representation
module _ where
  mutual
    Expr : List Type → Type → Set
    Expr Γ τ = TermF (Has Γ) (\ϕs ϕ → TermM (ϕs ++ Γ) ϕ) τ
  
    data TermM (Γ : List Type) : Type → Set where
      ret : ∀ {τ} → Has Γ τ → TermM Γ τ
      set : ∀ {ρ τ} → Expr Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
      --set : ∀ {σs ρ τ} → All (Has Γ) σs → Expr σs ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ

  compile : ∀ {Γ τ} → Term Γ τ → TermM Γ τ
  compile = {!!}

-- run-time representation
module _ where
  mutual
    ValueU : Type → Set
    ValueU τ = IntrF Value Closure τ

    data Value (τ : Type) : Set where
      wrap : ValueU τ → Value τ
  
    data Closure (ρs : List Type) (τ : Type) : Set where
      _&_ : ∀ {τs} → All Value τs → TermM (ρs ++ τs) τ → Closure ρs τ

  unwrapValue : ∀ {τ} → Value τ → ValueU τ
  unwrapValue (wrap v) = v
  
  Env : List Type → Set
  Env τs = All Value τs

  data CallStack : List Type → Type → Set where
    ε : ∀ {τ} → CallStack (single τ) τ
    _∷_ : ∀ {ρs σ τ} → Closure ρs σ → CallStack (single σ) τ → CallStack ρs τ

  Machine : Type → Set
  Machine τ = CallStack ε τ

  load : ∀ {τ} → TermM ε τ → Machine τ
  load term = (ε & term) ∷ ε

-- computation step
module _ where
  data Step (τ : Type) : Set where
    finish : Value τ → Step τ
    continue : Machine τ → Step τ

  applyClosure : ∀ {ρs τ} → Closure ρs τ → All Value ρs → Closure ε τ
  applyClosure (env & term) values = (values ++' env) & term

  apply = applyClosure

  {-
  composeEnvClosure : ∀ {σs τ} → Env σs → Closure σs τ → Closure ε τ
  composeEnvClosure values (env & term) = (values ++' env) & term

  composeValueClosure : ∀ {σ τ} → Value σ → Closure (single σ) τ → Closure ε τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  composeEnvStack : ∀ {σs τ} → Env σs → CallStack σs τ → Step τ
  composeEnvStack values (closure ∷ stack) = continue (composeEnvClosure values closure ∷ stack)
  composeEnvStack (value ∷ ε) ε = finish value

  composeValueStack : ∀ {σ τ} → Value σ → CallStack (single σ) τ → Step τ
  composeValueStack value ε = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)

  composeStackStack : ∀ {ρs σ τ} → CallStack ρs σ → CallStack (single σ) τ → CallStack ρs τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeStepStack : ∀ {ρ τ} → Step ρ → CallStack (single ρ) τ → Step τ
  --composeStepStack (finish value) stack = composeValueStack value stack
  composeStepStack (finish value) stack = composeEnvStack (single' value) stack
  composeStepStack (continue stack') stack = continue (composeStackStack stack' stack)
  -}

  stepIntrF : ∀ {τ} → IntrF Value Closure τ → Value τ
  stepIntrF rule = wrap rule

  --#caseMaybe : ∀ {τ ϕ} → TermM ε ϕ → TermM (single τ) ϕ → TermM (single (#Maybe τ)) ϕ
  --#caseMaybe = {!!}

  {-
       (step)
     FX  → X
      ↑    ↑ (fold)
    F μF → μF
      (wrap)
  -}
  -- fold : (#Maybe ϕ ⇒ ϕ) → (#Nat ⇒ ϕ)
  -- mapMaybe (fold _) : #Maybe #Nat ⇒ #Maybe ϕ
  -- step : #Maybe ϕ ⇒ ϕ
  -- fold ∘ wrap = step ∘ mapMaybe (fold _)
  --mapMaybe : Closure (single (#Maybe ϕ)) ϕ → Closure #Nat ϕ
  --mapMaybe : ∀ {σ τ} → Closure (single σ) τ → Closure (single (#Maybe σ)) (#Maybe τ)
  --mapMaybe : ∀ {σ τ} → Expr (single σ) τ → Closure (single (#Maybe σ)) (#Maybe τ)
  --mapMaybe = {!!}

  {- 
  -- compose : (σ ⇒ τ) → (ρ ⇒ σ) → (ρ ⇒ τ)
  compose : ∀ {ρ σ τ} → Closure (single σ) ρ → Closure (single ρ) τ → Closure (single σ) τ
  compose = {!!}

  natStep : ∀ {ϕ} → Closure (single (#Maybe ϕ)) ϕ → Term (single (#Maybe #Nat)) ϕ
  natStep closure = wrap (elim (var $0) ({!!} ∷ {!!} ∷ ε))
  -}

  stepElimF : ∀ {τ ϕ} → Value τ → ElimF Value Closure τ ϕ → Closure ε ϕ
  stepElimF {ρs ⇒ τ} (wrap closure) (refl , args) = applyClosure closure args
  stepElimF {#Sum τs} (wrap any-value) closures = getAllAny closures any-value (\closure value → apply closure (single' value))
  stepElimF {#Product τs} (wrap values) any-closure = getAllAny values any-closure (\value closure → apply closure (single' value))
  stepElimF {#Nat} (wrap value) closure = apply {!compose (mapMaybe (elim $0 closure)) closure !} (single' value) --(value ∷ {!!}) & set (elim $0 (set {!elim $!} (ret $0) ∷ {!!} ∷ ε)) (ret $0)
  stepElimF {#List τ} (wrap value) rule = {!!}
  stepElimF {#Tree τ} (wrap value) rule = {!!}
  stepElimF {#Conat} (wrap value) rule = {!!}
  stepElimF {#Stream τ} (wrap value) rule = {!!}

  --mapMaybe : ∀ {σ τ} → Expr (single σ) τ → Closure (single (#Maybe σ)) (#Maybe τ)
  mapMaybe : ∀ {Γ σ τ} → (Has Γ σ → TermM Γ τ) → TermM (#Maybe σ ∷ Γ) (#Maybe τ)
  mapMaybe = {!!}

  applyTerm : ∀ {Γ σ τ} → TermM (σ ∷ Γ) τ → TermM Γ σ → TermM Γ τ
  applyTerm = {!!}

  -- compose : (σ ⇒ τ) → (ρ ⇒ σ) → (ρ ⇒ τ)
  compose : ∀ {Γ ρ σ τ} → TermM (σ ∷ Γ) τ → TermM (ρ ∷ Γ) σ → TermM (ρ ∷ Γ) τ
  compose = {!applyTerm!}

  natStep : ∀ {Γ ϕ} → Env Γ → TermM (#Maybe ϕ ∷ Γ) ϕ → TermM (#Maybe #Nat ∷ Γ) ϕ
  natStep env step = compose step (mapMaybe \v → set (elim v step) (ret $0))

  --rename : ∀ {Γ Γ' τ} → → Term Γ τ → Term Γ' τ
  drop2 : ∀ {Γ ρ σ τ} → TermM (ρ ∷ Γ) τ → TermM (ρ ∷ σ ∷ Γ) τ 
  drop2 = {!!}

  stepElimF' : ∀ {τ Γ ϕ} → Env Γ → Value τ → ElimF (Has Γ) (\ϕs ϕ → TermM (ϕs ++ Γ) ϕ) τ ϕ → Closure ε ϕ
  stepElimF' {#Nat} env (wrap value) step = (value ∷ env) & compose step (mapMaybe \v → {!!})
    {-
    (value ∷ env)
    & set (elim $0
        ( set (intr (here $0)) (
          ret $0)
        ∷ set (elim $0 (drop2 (drop2 term))) (
          set (intr (there (here $0))) (
          ret $0))
        ∷ ε)
      )
      (drop2 term)
      -}
  stepElimF' {τ} env value rule = {!!}

  step : ∀ {τ} → Machine τ → Step τ
  step ((env & ret x) ∷ ε) = finish (get env x)
  step ((env & ret x) ∷ closure ∷ stack) = continue (closure' ∷ stack)
    where
      closure' : Closure ε _
      closure' = apply closure (single' (get env x))
  step ((env & set (intr {τ} rule) term) ∷ stack) = continue (((value ∷ env) & term) ∷ stack)
    where
      value : Value τ
      value = stepIntrF (mapIntrF (\x → get env x) (\term → (env & term)) {τ} rule)
  step ((env & set (elim {τ} {ϕ} x rule) term) ∷ stack) = continue (closure ∷ (env & term) ∷ stack)
    where
      closure : Closure ε ϕ
      closure = stepElimF (get env x) (mapElimF (\x → get env x) (\term → (env & term)) {τ} {ϕ} rule)

  {-
  applyFunction : ∀ {ρs τ} → Value (ρs ⇒ τ) → All Value ρs → Closure ε τ
  applyFunction = {!!}

  applySum : ∀ {Γ τs ϕ} → Env Γ → Value (#Sum τs) → All (\τ → TermM (τ ∷ Γ) ϕ) τs → Closure ε ϕ
  applySum = {!!}

  applyProduct : ∀ {Γ τs ϕ} → Env Γ → Value (#Product τs) → Any (\τ → TermM (τ ∷ Γ) ϕ) τs → Closure ε ϕ
  applyProduct = {!!}

  applyNat : ∀ {Γ ϕ} → Env Γ → Value #Nat → TermM (#Maybe ϕ ∷ Γ) ϕ → Machine ϕ
  applyNat = {!!}

  applyList : ∀ {Γ τ ϕ} → Env Γ → Value (#List τ) → TermM (#Maybe (#Pair τ ϕ) ∷ Γ) ϕ → Machine ϕ
  applyList = {!!}

  #forceConat : Value #Conat → Machine (#Maybe #Conat)
  #forceConat (wrap (ρ ,, value , closure)) = {!apply closure (single' value) !} ∷ ε

  --applyConat : ∀ {Γ ϕ} → Env Γ → Value #Conat → TermM (#Maybe #Conat ∷ Γ) ϕ → Machine ϕ
  --applyConat env (wrap (ρ ,, value , closure)) term = apply closure (single' value) ∷ {!env & term!} ∷ ε

  -- Has Γ ϕ → Value ϕ
  -- Env Γ, TermM (ϕs ++ Γ) ϕ → Closure ϕs ϕ
  stepExpr : ∀ {Γ τ} → Env Γ → Expr Γ τ → Step τ
  stepExpr {Γ} {τ} env (elim {ρs ⇒ τ} f (refl , xs)) = continue (applyFunction (get env f) (mapAll (get env) xs) ∷ ε) -- ((values ++ env) & get env f) ∷ ε
  stepExpr {Γ} {ϕ} env (elim {#Sum τs} e terms) = continue (applySum env (get env e) terms ∷ ε)
  stepExpr {Γ} {ϕ} env (elim {#Product τs} p any-term) = continue (applyProduct env (get env p) any-term ∷ ε)
  stepExpr {Γ} {ϕ} env (elim {#Nat} n term) = continue (applyNat env (get env n) term)
  stepExpr {Γ} {ϕ} env (elim {#List τ} l term) = continue (applyList env (get env l) term)
  stepExpr {Γ} {ϕ} env (elim {#Conat} x refl) = continue (#forceConat (get env x))
  --stepExpr {Γ} {ϕ} env (elim {#Conat} x term) = continue (applyConat env (get env x) term)
  stepExpr {Γ} {_} env (elim {#Stream τ} expr eq) = {!!}
  stepExpr {Γ} {ρs ⇒ τ} env (intr {τ = ρs ⇒ τ} term) = finish (wrap (env & term))
  stepExpr {Γ} {#Sum τs} env (intr {τ = #Sum τs} any-var) = finish (wrap (mapAny (\x → get env x) any-var))
  stepExpr {Γ} {#Product τs} env (intr {τ = #Product τs} vars) = finish (wrap (mapAll (\x → get env x) vars))
  stepExpr {Γ} {#Nat} env (intr {τ = #Nat} x) = finish (wrap (get env x))
  stepExpr {Γ} {#List τ} env (intr {τ = #List τ} x) = finish (wrap (get env x))
  stepExpr {Γ} {#Conat} env (intr {τ = #Conat} (ρ ,, x , term)) = finish (wrap (ρ ,, get env x , (env & term)))
  stepExpr {Γ} {#Stream τ} env (intr {τ = #Stream τ} (ρ ,, x , term)) = finish (wrap (ρ ,, get env x , (env & term)))

  stepClosure : ∀ {τ} → Closure ε τ → Step τ
  stepClosure (env & ret x) = finish (get env x)
  stepClosure (env & set expr term) = composeStepStack (stepExpr env expr) ((env & term) ∷ ε)

  step : ∀ {τ} → Machine τ → Step τ
  step (closure ∷ stack) = composeStepStack (stepClosure closure) stack
  -}

-- composeStepStack (step machine) cont ≡ step (composeStackStack machine cont)
module _ where
 {-
  eq-composeStepStack :
    ∀ {σ τ} (machine : Machine σ) (stack : CallStack (single σ) τ)
    → composeStepStack (step machine) stack ≡ step (composeStackStack machine stack)
    -}
  eq-composeStepStack : {!!}
  eq-composeStepStack = {!!}

-- run
module _ where
  Val : Type → Set₁
  Val τ = Value τ → Set

  AllVal : List Type → Set₁
  AllVal τs = All₁ (\τ → Value τ → Set) τs

  data TraceStepF {τ} (%GoodValue : Val τ) : Step τ → Set where
    goodFinish : {value : Value τ} → %GoodValue value → TraceStepF %GoodValue (finish value)
    goodContinue : {machine : Machine τ} → TraceStepF %GoodValue (step machine) → TraceStepF %GoodValue (continue machine)

  TraceClosureF : ∀ {τ} → (%Good-τ : Val τ) → Closure ε τ → Set
  TraceClosureF {τ} %Good-τ closure = TraceStepF %Good-τ (continue (closure ∷ ε))

  -- good types
  module _ where
    AllGoodF : ∀ {τs} → All₁ Val τs → All Value τs → Set
    AllGoodF {ε} ε ε = ⊤
    AllGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (value ∷ values) = Good-τ value × AllGoodF Good-τs values

    AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set
    AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (here value) = Good-τ value
    AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (there any-value) = AnyGoodF Good-τs any-value
    --data AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set where
    --  here : ∀ {τ τs} {Good-τ : Val τ} {Good-τs : All₁ Val τs} {value} → Good-τ value → AnyGoodF (Good-τ ∷ Good-τs) (here value)
    --  there : ∀ {τ τs} {Good-τ Good-τs any-value} → AnyGoodF {τs} Good-τs any-value → AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (there any-value)

    Good-⇒ : ∀ {ρs τ} → AllVal ρs → Val τ → Val (ρs ⇒ τ)
    Good-⇒ {ρs} {τ} Good-ρs Good-τ (wrap closure) = {values : All Value ρs} → AllGoodF Good-ρs values → TraceClosureF Good-τ (apply closure values)

    Good-Sum : ∀ {τs} → AllVal τs → Val (#Sum τs)
    Good-Sum Good-τs (wrap any-value) = AnyGoodF Good-τs any-value

    Good-Product : ∀ {τs} → AllVal τs → Val (#Product τs)
    Good-Product Good-τs (wrap values) = AllGoodF Good-τs values

    Good-Void : Val #Void
    Good-Void = Good-Sum ε
    
    Good-Unit : Val #Unit
    Good-Unit = Good-Product ε
    
    Good-Either : ∀ {σ τ} → Val σ → Val τ → Val (#Either σ τ)
    Good-Either Good-σ Good-τ = Good-Sum (Good-σ ∷ Good-τ ∷ ε)
    
    Good-Pair : ∀ {σ τ} → Val σ → Val τ → Val (#Pair σ τ)
    --Good-Pair Good-σ Good-τ = Good-Product (Good-σ ∷ Good-τ ∷ ε)
    Good-Pair Good-σ Good-τ (wrap (value1 ∷ value2 ∷ ε)) = Good-σ value1 × Good-τ value2 × ⊤
    
    Good-Maybe : ∀ {τ} → Val τ → Val (#Maybe τ)
    --Good-Maybe Good-τ = Good-Sum (Good-Unit ∷ Good-τ ∷ ε)
    Good-Maybe Good-τ (wrap (here unit)) = ⊤
    Good-Maybe Good-τ (wrap (there (here value))) = Good-τ value

    #inl : ∀ {σ τ} → Value σ → Value (#Either σ τ)
    #inl value = wrap (here value)

    #inr : ∀ {σ τ} → Value τ → Value (#Either σ τ)
    #inr value = wrap (there (here value))

    #unit : Value #Unit
    #unit = wrap ε

    #pair : ∀ {σ τ} → Value σ → Value τ → Value (#Pair σ τ)
    #pair value1 value2 = wrap (value1 ∷ value2 ∷ ε)

    #zero : Value #Nat
    #zero = wrap (#inl #unit)
  
    #succ : Value #Nat → Value #Nat
    #succ n = wrap (#inr n)
  
    #nil : ∀ {τ} → Value (#List τ)
    #nil = wrap (#inl #unit)
  
    #cons : ∀ {τ} → Value τ → Value (#List τ) → Value (#List τ)
    #cons head tail = wrap (#inr (#pair head tail))
  
    data Good-Nat : Value #Nat → Set where
      zero : Good-Nat #zero
      succ : {n : Value #Nat} → Good-Nat n → Good-Nat (#succ n)
  
    data Good-List {τ} (%Good-τ : Value τ → Set) : Value (#List τ) → Set where
      nil : Good-List %Good-τ #nil
      cons : {v : Value τ} {l : Value (#List τ)} → %Good-τ v → Good-List %Good-τ l → Good-List %Good-τ (#cons v l)

    module _ where
      record Good-Conat' {ρ} (closure : Closure (single ρ) (#Maybe ρ)) (value : Value ρ) : Set where
        coinductive
        field force : TraceClosureF (Good-Maybe (Good-Conat' closure)) (apply closure (single' value))

      Good-Conat : Val #Conat
      Good-Conat (wrap (ρ ,, value , closure)) = Good-Conat' closure value

    module _ {τ} (%Good-τ : Val τ) where
      record Good-Stream' {ρ} (closure : Closure (single ρ) (#Pair τ ρ)) (value : Value ρ) : Set where
        coinductive
        field force : TraceClosureF (Good-Pair %Good-τ (Good-Stream' closure)) (apply closure (single' value))

      Good-Stream : Val (#Stream τ)
      Good-Stream (wrap (ρ ,, value , closure)) = Good-Stream' closure value

  mutual
    GoodValue : ∀ {τ} → Val τ
    GoodValue = {!!}
    {-
    GoodValue {ρs ⇒ τ} = Good-⇒ (AllGoodValue {ρs}) (GoodValue {τ})
    GoodValue {#Sum τs} = Good-Sum (AllGoodValue {τs})
    GoodValue {#Product τs} = Good-Product (AllGoodValue {τs})
    GoodValue {#Nat} = Good-Nat
    GoodValue {#List τ} = Good-List (GoodValue {τ})
    GoodValue {#Conat} = Good-Conat
    GoodValue {#Stream τ} = Good-Stream (GoodValue {τ})
    -}

    AllGoodValue : ∀ {τs} → AllVal τs
    AllGoodValue {ε} = ε
    AllGoodValue {τ ∷ τs} = GoodValue {τ} ∷ AllGoodValue {τs}

  TraceStep : ∀ {τ} → Step τ → Set
  TraceStep = TraceStepF GoodValue

  Trace : ∀ {τ} → Machine τ → Set
  Trace machine = TraceStep (continue machine)

  {-
  TraceStack : ∀ {ρs τ} → CallStack ρs τ → Set
  TraceStack {ρs} {τ} stack = {env : Env ρs} → All2 GoodValue env → TraceStep (composeEnvStack env stack)
  -}

  TraceClosureε : ∀ {τ} → Closure ε τ → Set
  TraceClosureε {τ} closure = Trace (closure ∷ ε)

  TraceClosure : ∀ {ρs τ} → Closure ρs τ → Set
  TraceClosure {ρs} {τ} closure = {env : Env ρs} → All2 GoodValue env → Trace (apply closure env ∷ ε)

  TraceTermM : ∀ {ρs τ} → TermM ρs τ → Set
  TraceTermM {ρs} {τ} term = {env : Env ρs} → All2 GoodValue env → Trace ((env & term) ∷ ε)

  --Trace : ∀ {ρs τ} → TermM ρs τ → Set
  --Trace = TraceTermM

  data AllTraceStack : ∀ {ρs τ} → CallStack ρs τ → Set where
    ε : ∀ {τ} → AllTraceStack {single τ} {τ} ε
    _∷_ :
      ∀ {ρs σ τ} {closure : Closure ρs σ} {stack : CallStack (single σ) τ}
      → TraceClosure closure → AllTraceStack stack → AllTraceStack (closure ∷ stack)

  AllTraceExpr : ∀ {ρs τ} → Expr ρs τ → Set
  AllTraceExpr = {!!}
  {-
  AllTraceExpr (elim {τ = ρs ⇒ τ} _ e) = ⊤
  AllTraceExpr (elim {τ = #Sum τs} _ terms) = All2 TraceTermM terms
  AllTraceExpr (elim {τ = #Product τs} _ any-term) = IsAny TraceTermM any-term
  AllTraceExpr (elim {τ = #Nat} _ term) = TraceTermM term
  AllTraceExpr (elim {τ = #List τ} _ term) = TraceTermM term
  AllTraceExpr (elim {τ = #Conat} _ _) = ⊤
  AllTraceExpr (elim {τ = #Stream τ} _ _) = ⊤
  AllTraceExpr (intr {τ = ρs ⇒ τ} term) = TraceTermM term
  AllTraceExpr (intr {τ = #Sum τs} any-value) = ⊤
  AllTraceExpr (intr {τ = #Product τs} values) = ⊤
  AllTraceExpr (intr {τ = #Nat} _) = ⊤
  AllTraceExpr (intr {τ = #List τ} value) = ⊤
  AllTraceExpr (intr {τ = #Conat} (ρ ,, value , term)) = TraceTermM term
  AllTraceExpr (intr {τ = #Stream τ} (ρ ,, value , term)) = TraceTermM term
  -}

  {-
  trace-allTraceStack : ∀ {ρs τ} {stack : CallStack ρs τ} → AllTraceStack stack → TraceStack stack
  trace-allTraceStack = {!!}
  -}

  {-
  trace-stepExpr :
    ∀ {Γ τ} {expr : Expr Γ τ} {env : All Value Γ}
    → All2 GoodValue env → AllTraceExpr expr → TraceStep (stepExpr env expr)
  trace-stepExpr = {!!}
  -}

  {-
  trace-composeValueStack :
    ∀ {σ τ value stack}
    → GoodValue {σ} value → AllTraceStack {single σ} {τ} stack → TraceStep (composeValueStack value stack)
  trace-composeValueStack = {!!}
  -}

  {-
  trace-composeStepStack :
    ∀ {ρ τ} {step : Step ρ} {stack : CallStack (single ρ) τ}
    → TraceStep step → TraceStack stack → TraceStep (composeStepStack step stack)
  trace-composeStepStack = {!!}
  -}

  mutual
    traceTermM : ∀ {Γ τ} → (term : TermM Γ τ) → TraceTermM term
    traceTermM (ret x) good-env = goodContinue (goodFinish (get2 good-env x))
    traceTermM (set expr term) {env = env} good-env = {!!}
    {-
    traceTermM (set expr term) {env = env} good-env = goodContinue
      ( trace-composeStepStack {step = composeStepStack (stepExpr env expr) ((env & term) ∷ ε)} {stack = ε}
          ( trace-composeStepStack {step = stepExpr env expr} {stack = (env & term) ∷ ε}
              (trace-stepExpr {expr = expr} good-env (allTraceExpr expr))
              (trace-allTraceStack ((\good-env' → traceTermM term (good-env' ++2 good-env)) ∷ ε))
          )
          (trace-allTraceStack ε)
      )
      -}

    allTraceExpr : ∀ {ρs τ} → (expr : Expr ρs τ) → AllTraceExpr expr
    allTraceExpr = {!!}
    {-
    allTraceExpr (elim {τ = ρs ⇒ τ} _ e) = tt
    allTraceExpr (elim {τ = #Sum τs} _ terms) = allTraceTermM terms where
      allTraceTermM : ∀ {ρs τs ϕ} → (terms : All (\τ → TermM (τ ∷ ρs) ϕ) τs) → All2 TraceTermM terms
      allTraceTermM ε = ε
      allTraceTermM (term ∷ terms) = traceTermM term ∷ allTraceTermM terms
    allTraceExpr (elim {τ = #Product τs} _ any-term) = anyTraceTermM any-term where
      anyTraceTermM : ∀ {ρs τs ϕ} → (any-term : Any (\τ → TermM (τ ∷ ρs) ϕ) τs) → IsAny TraceTermM any-term
      anyTraceTermM (here term) = traceTermM term
      anyTraceTermM (there any-term) = anyTraceTermM any-term
    allTraceExpr (elim {τ = #Nat} _ term) = traceTermM term
    allTraceExpr (elim {τ = #List τ} _ term) = traceTermM term
    allTraceExpr (elim {τ = #Conat} _ _) = tt
    allTraceExpr (elim {τ = #Stream τ} _ _) = tt
    allTraceExpr (intr {τ = ρs ⇒ τ} term) = traceTermM term
    allTraceExpr (intr {τ = #Sum τs} any-value) = tt
    allTraceExpr (intr {τ = #Product τs} values) = tt
    allTraceExpr (intr {τ = #Nat} _) = tt
    allTraceExpr (intr {τ = #List τ} value) = tt
    allTraceExpr (intr {τ = #Conat} (_ ,, _ , term)) = traceTermM term
    allTraceExpr (intr {τ = #Stream τ} (_ ,, _ , term)) = traceTermM term
    -}

  mutual
    goodValue : ∀ {τ} → (value : Value τ) → GoodValue value
    goodValue = {!!}
    {-
    goodValue {ρs ⇒ τ} (wrap closure) = {!traceClosure closure!}
    goodValue {#Sum τs} value = {!!}
    goodValue {#Product τs} value = {!!}
    goodValue {#Nat} value = {!!}
    goodValue {#List τ} value = {!!}
    goodValue {#Conat} value = {!!}
    goodValue {#Stream τ} value = {!!}
    -}

    traceClosure : ∀ {ρs τ} → (closure : Closure ρs τ) → TraceClosure closure
    traceClosure (env & term) = {!!}

  run : ∀ {τ} → (machine : Machine τ) → Trace machine
  run (closure ∷ machine) = {!traceClosure closure!}

  result : ∀ {τ} {machine : Machine τ} → Trace machine → Value τ
  result trace = resultStep trace where
    resultStep : ∀ {τ} {step : Step τ} → TraceStep step → Value τ
    resultStep (goodFinish {value} _good-value) = value
    resultStep (goodContinue trace) = resultStep trace

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))

{-
Type : Set

- Term -- de brujin term
- TermM -- compiled representation (assignment sequence)
- Machine -- run-time representation
- Value -- computation result
- Trace -- computation trace
- GoodValue -- denotation

- compile : Term ε τ → TermM ε τ
- load : TermM ε τ → Machine τ
- step : Machine τ → Value τ + Machine τ
- run : Machine τ → Trace τ
- result : Trace τ → Value τ
- evaluate : Term ε τ → Value τ
-}
