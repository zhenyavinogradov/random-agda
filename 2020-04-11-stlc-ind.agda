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

  ∃ : {A : Set} → (A → Set) → Set
  ∃ {A} B = Σ A B

  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

  Eq = _≡_

  infixr 15 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data Has {A : Set} : List A → A → Set where
    here : ∀ {a as} → Has (a ∷ as) a
    there : ∀ {a b as} → Has as a → Has (b ∷ as) a

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  data All₁ {A : Set} (P : A → Set₁) : List A → Set₁ where
    ε : All₁ P ε
    _∷_ : ∀ {a as} → P a → All₁ P as → All₁ P (a ∷ as)

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

  data All2 {A : Set} {P : A → Set} (P2 : {a : A} → P a → Set) : {as : List A} → All P as → Set where
    ε : All2 P2 ε
    _∷_ : ∀ {a as Pa Pas} → P2 Pa → All2 P2 {as} Pas → All2 P2 {a ∷ as} (Pa ∷ Pas)

  IsAny : {A : Set} {P : A → Set} → (P2 : {a : A} → P a → Set) → {as : List A} → Any P as → Set
  IsAny P2 (here Pa) = P2 Pa
  IsAny P2 (there any-Pa) = IsAny P2 any-Pa

  transport : {A : Set} {a b : A} → (P : A → Set) → a ≡ b → P a → P b
  transport P refl Pa = Pa

  cong : {A B : Set} {a a' : A} → (f : A → B) → a ≡ a' → f a ≡ f a'
  cong f refl = refl

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

  $0 : ∀ {A a0 as} → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as} → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $0 = here
  $1 = there here
  $2 = there (there here)
  $3 = there (there (there here))

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
    intr : ∀ τ → IntrF τ → TermF τ
    elim : ∀ τ ϕ → %Value τ → ElimF τ ϕ → TermF ϕ

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
  EnvSgn : Set
  EnvSgn = List Type

  TextSgn : Set
  TextSgn = List (List Type × Type)

  mutual
    Expr : EnvSgn → TextSgn → Type → Set
    Expr Γ Θ τ = TermF (Has Γ) (\ϕs ϕ → Has Θ (ϕs , ϕ)) τ
  
    data TermM (Γ : EnvSgn) (Θ : TextSgn) : Type → Set where
      return : ∀ {τ} → Has Γ τ → TermM Γ Θ τ
      set-closure : ∀ ρs ρ {τ} → TermM (ρs ++ Γ) Θ ρ → TermM Γ ((ρs , ρ) ∷ Θ) τ → TermM Γ Θ τ
      set-value : ∀ ρ {τ} → Expr Γ Θ ρ → TermM (ρ ∷ Γ) Θ τ → TermM Γ Θ τ

  infixr 5 _▸_
  _▸_ : ∀ {Γ Θ ρ τ} → Expr Γ Θ ρ → TermM (ρ ∷ Γ) Θ τ → TermM Γ Θ τ
  _▸_ = set-value _

  infixr 5 _▹_
  _▹_ : ∀ {Γ Θ ρs ρ τ} → TermM (ρs ++ Γ) Θ ρ → TermM Γ ((ρs , ρ) ∷ Θ) τ → TermM Γ Θ τ
  _▹_ = set-closure _ _


  compile : ∀ {τ} → Term ε τ → TermM ε ε τ
  compile = {!!}

-- run-time representation
module _ where
  mutual
    ValueU : Type → Set
    ValueU τ = IntrF Value Closure τ

    data Value (τ : Type) : Set where
      wrap : ValueU τ → Value τ
  
    data Closure (ρs : List Type) (τ : Type) : Set where
      _&_ : ∀ {Γ Θ} → Heap Γ Θ → TermM (ρs ++ Γ) Θ τ → Closure ρs τ

    Heap : (Γ : EnvSgn) → (Θ : TextSgn) → Set
    Heap Γ Θ = All (\ϕ → Value ϕ) Γ × All (\{ (ϕs , ϕ) → Closure ϕs ϕ }) Θ

  Env : EnvSgn → Set
  Env Γ = All Value Γ

  Text : TextSgn → Set
  Text Θ = All (\{ (ϕs , ϕ) → Closure ϕs ϕ }) Θ

  data CallStack : List Type → Type → Set where
    ε : ∀ {τ} → CallStack (single τ) τ
    _∷_ : ∀ {ρs σ τ} → Closure ρs σ → CallStack (single σ) τ → CallStack ρs τ

  Machine : Type → Set
  Machine τ = CallStack ε τ

  load : ∀ {τ} → TermM ε ε τ → Machine τ
  load term = ((ε , ε) & term) ∷ ε

-- computation step
module _ where
  data Step (τ : Type) : Set where
    finish : Value τ → Step τ
    continue : Machine τ → Step τ

  applyClosure : ∀ {ρs τ} → Closure ρs τ → All Value ρs → Closure ε τ
  -- applyClosure (env & term) values = (values ++' env) & term
  applyClosure ((env , txt) & term) values = ((values ++' env) , txt) & term

  apply = applyClosure

  {-
  stepIntrF : ∀ {τ} → IntrF Value Closure τ → Value τ
  stepIntrF rule = wrap rule

  stepElimF : ∀ {τ ϕ} → Value τ → ElimF Value Closure τ ϕ → Closure ε ϕ
  stepElimF {ρs ⇒ τ} (wrap closure) (refl , args) = apply closure args
  stepElimF {#Sum τs} (wrap any-value) closures = getAllAny closures any-value (\closure value → apply closure (single' value))
  stepElimF {#Product τs} (wrap values) any-closure = getAllAny values any-closure (\value closure → apply closure (single' value))
  stepElimF {#Nat} (wrap value) closure = apply {!compose (mapMaybe (elim $0 closure)) closure !} (single' value) --(value ∷ {!!}) & set (elim $0 (set {!elim $!} (ret $0) ∷ {!!} ∷ ε)) (ret $0)
  stepElimF {#List τ} (wrap value) rule = {!!}
  stepElimF {#Tree τ} (wrap value) rule = {!!}
  stepElimF {#Conat} (wrap value) rule = {!!}
  stepElimF {#Stream τ} (wrap value) rule = {!!}
  -}

  pure : ∀ {Γ Θ τ} → Expr Γ Θ τ → TermM Γ Θ τ
  pure expr = set-value _ expr (return here)

  composeStackStack : ∀ {ρs σ τ} → CallStack ρs σ → CallStack (single σ) τ → CallStack ρs τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeMachineStack : ∀ {σ τ} → Machine σ → CallStack (single σ) τ → Machine τ
  composeMachineStack = composeStackStack

  pureStack : ∀ {ρs τ} → Closure ρs τ → CallStack ρs τ
  pureStack closure = closure ∷ ε

  --applyTerm : ∀ {Γ σ τ} → TermM (σ ∷ Γ) τ → TermM Γ σ → TermM Γ τ
  --applyTerm = {!!}

  -- compose : (σ ⇒ τ) → (ρ ⇒ σ) → (ρ ⇒ τ)
  --compose : ∀ {Γ ρ σ τ} → TermM (ρ ∷ Γ) σ → TermM (σ ∷ Γ) τ → TermM (ρ ∷ Γ) τ
  --compose = {!applyTerm!}

  --caseMaybe : ∀ {Γ ϕ τ} → TermM Γ ϕ → TermM (τ ∷ Γ) ϕ → TermM (#Maybe τ ∷ Γ) ϕ
  --caseMaybe {ϕ = ϕ} {τ = τ} termN termJ = pure (elim (#Maybe τ) ϕ $0 ({!!} ∷ ({!!} ∷ ε)))

  --#nothing : ∀ {Γ τ} → TermM Γ (#Maybe τ)
  --#nothing = {!!}

  --#just : ∀ {Γ τ} → TermM Γ τ → TermM Γ (#Maybe τ)
  --#just = {!!}

  --mapMaybe : ∀ {σ τ} → Expr (single σ) τ → Closure (single (#Maybe σ)) (#Maybe τ)
  --mapMaybe : ∀ {Γ σ τ} → (Has Γ σ → TermM Γ τ) → TermM (#Maybe σ ∷ Γ) (#Maybe τ)
  --mapMaybe f = caseMaybe #nothing {!!}

  --mapMaybe : ∀ {σ τ} → TermM ((single σ ⇒ τ) ∷ #Maybe σ ∷ ε) (#Maybe τ)
  --mapMaybe = {!!}

  --rename : ∀ {Γ Γ' τ} → → Term Γ τ → Term Γ' τ
  --drop2 : ∀ {Γ ρ σ τ} → TermM (ρ ∷ Γ) τ → TermM (ρ ∷ σ ∷ Γ) τ 
  --drop2 = {!!}
  {-
  stepElimF : ∀ {Γ Θ} → ∀ τ ϕ → Heap Γ Θ → Value τ → ElimF (Has Γ) (\ϕs ϕ → TermM (ϕs ++ Γ) ε ϕ) τ ϕ → Machine ϕ
  stepElimF (ρs ⇒ τ) ϕ (env , txt) (wrap (env' & term)) (refl , args) = {!!} --((mapAll (get env) args ++' env') & term) ∷ ε
  stepElimF (#Sum τs) ϕ (env , txt) (wrap any-value) terms = {!!} --getAllAny terms any-value (\term value → (value ∷ env) & term) ∷ ε
  stepElimF (#Product τs) ϕ (env , txt) (wrap values) any-term = {!!} --getAllAny values any-term (\value term → (value ∷ env) & term) ∷ ε
  --stepElimF (#Nat) ϕ env (wrap value) step = ((stepFunction ∷ value ∷ ε) & mapMaybe) ∷ (env & step) ∷ ε
  stepElimF (#Nat) ϕ env (wrap value) step = {!!}
    where
      stepFunction : Value (single #Nat ⇒ ϕ)
      stepFunction = {!!} --wrap (env & pure (elim #Nat ϕ $0 {!step!}))
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
  stepElimF {τ} env value rule = {!!}
  -}

  {-
  --mapMaybe : ∀ {σ τ} ? → → TermM (#Maybe σ ∷ ε) ((single σ , τ) ∷ ε) (#Maybe τ)
  mapMaybe : ∀ {σ τ} → {!!} → TermM (#Maybe σ ∷ ε) ε (#Maybe τ)
  mapMaybe {σ} {τ} _ =
    set-closure (single #Unit) (#Maybe τ)
      (pure (intr (#Maybe τ) (here $0))) (
    set-closure (single σ) (#Maybe τ)
      {!!} (
    pure (elim (#Maybe σ) (#Maybe τ) $0
    ( $1
    ∷ $0
    ∷ ε
    ))))
    -}

  mapElimMaybe : ∀ {ϕ} → TermM (#Maybe #Nat ∷ ε) ((single (#Maybe ϕ) , ϕ) ∷ ε) (#Maybe ϕ)
  mapElimMaybe {ϕ} =
    ( intr (#Maybe ϕ) (here $0) ▸
      return $0
    ) ▹
    ( elim #Nat ϕ $0 $1 ▸
      intr (#Maybe ϕ) (there (here $0)) ▸
      return $0
    ) ▹
    elim (#Maybe #Nat) (#Maybe ϕ) $0 ($1 ∷ $0 ∷ ε) ▸
    return $0

  stepElimF : ∀ τ ϕ → Value τ → ElimF Value Closure τ ϕ → Machine ϕ
  stepElimF (ρs ⇒ τ) .τ (wrap closure) (refl , values) = apply closure values ∷ ε
  stepElimF (#Sum τs) ϕ (wrap any-value) closures = getAllAny closures any-value (\closure value → apply closure (value ∷ ε)) ∷ ε
  stepElimF (#Product τs) ϕ (wrap values) any-closure = getAllAny values any-closure (\value closure → apply closure (value ∷ ε)) ∷ ε
  --stepElimF' #Nat ϕ (wrap value) step = (((value ∷ ε) , (((ε , step ∷ ε) & pure (elim #Nat ϕ $0 $0)) ∷ ε)) & mapMaybe ?) ∷ step ∷ ε
  stepElimF #Nat ϕ (wrap value) step = (((value ∷ ε) , (step ∷ ε)) & mapElimMaybe) ∷ step ∷ ε
  stepElimF _ ϕ value rule = {!!}

  step : ∀ {τ} → Machine τ → Step τ
  step (((env , txt) & return x) ∷ ε) = finish (get env x)
  step (((env , txt) & return x) ∷ ((env' , txt') & term) ∷ stack) = continue ((((get env x ∷ env') , txt') & term) ∷ stack)
  step (((env , txt) & (set-closure _ _ term cont)) ∷ stack) = continue (((env , ((env , txt) & term) ∷ txt) & cont) ∷ stack)
  step (((env , txt) & (set-value _ (intr τ rule) cont)) ∷ stack) = continue ((((value ∷ env) , txt) & cont) ∷ stack)
    where
      value : Value τ
      value = wrap (mapIntrF (\x → get env x) (\x → get txt x) {τ} rule)
  step (((env , txt) & (set-value _ (elim τ ϕ x rule) cont)) ∷ stack) = continue (composeMachineStack machine (((env , txt) & cont) ∷ stack))
    where
      machine : Machine ϕ
      machine = stepElimF τ ϕ (get env x) (mapElimF (\x → get env x) (\x → get txt x) {τ} rule)

module Test where
  num : ∀ Γ Θ → ℕ → TermM Γ Θ #Nat
  num Γ Θ n =
      intr #Unit ε ▸
      intr (#Maybe #Nat) (here $0) ▸
      intr #Nat $0 ▸
      go n
    where
      go : ∀ {Γ} → ℕ → TermM (#Nat ∷ Γ) Θ #Nat
      go zero = return $0
      go (succ n) =
        intr (#Maybe #Nat) (there (here $0)) ▸
        intr #Nat $0 ▸
        go n
  
  add : ∀ Γ Θ → TermM (#Nat ∷ #Nat ∷ Γ) Θ #Nat
  add _ _ =
    return $2 ▹
    ( intr (#Maybe #Nat) (there (here $0)) ▸
      intr #Nat $0 ▸
      return $0
    ) ▹
    pure (elim (#Maybe #Nat) #Nat $0 ($1 ∷ $0 ∷ ε)) ▹
    elim #Nat #Nat $0 $0 ▸
    return $0
  
  stepn : {τ : Type} → ℕ → Machine τ → Step τ
  stepn zero s = continue s
  stepn (succ n) s with step s
  … | finish v = finish v
  … | continue s' = stepn n s'
  
  run : ∀ {τ} → ℕ → TermM ε ε τ → Step τ
  run i term = stepn i (load term)
  
  test : TermM ε ε #Nat
  test =
    num _ _ 3 ▹
    intr (ε ⇒ #Nat) $0 ▸
    elim (ε ⇒ #Nat) #Nat $0 (refl , ε) ▸
    num _ _ 2 ▹
    intr (ε ⇒ #Nat) $0 ▸
    elim (ε ⇒ #Nat) _ $0 (refl , ε) ▸
    add _ _ ▹
    intr ((#Nat ∷ #Nat ∷ ε) ⇒ #Nat) $0 ▸
    elim ((#Nat ∷ #Nat ∷ ε) ⇒ #Nat) _ $0 (refl , $1 ∷ $3 ∷ ε) ▸
    return $0
  
  _ : {!!}
  _ = {!run 70 test!}

-- run
module _ where
  Trace : ∀ {τ} → Machine τ → Set
  Trace machine = {!!}

  run : ∀ {τ} → (machine : Machine τ) → Trace machine
  run (closure ∷ machine) = {!traceClosure closure!}

  result : ∀ {τ} {machine : Machine τ} → Trace machine → Value τ
  result trace = {!!}

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate {τ} term = {!result (run (load (compile term)))!}

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
