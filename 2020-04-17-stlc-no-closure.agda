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

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  data All₁ {A : Set} (P : A → Set₁) : List A → Set₁ where
    ε : All₁ P ε
    _∷_ : ∀ {a as} → P a → All₁ P as → All₁ P (a ∷ as)

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

  {-
  data Has {A : Set} : List A → A → Set where
    here : ∀ {a as} → Has (a ∷ as) a
    there : ∀ {a b as} → Has as a → Has (b ∷ as) a
  -}
  Has : {A : Set} → List A → A → Set
  Has as a = Any (Eq a) as


  data AllAll {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → All P as → Set where
    ε : AllAll P2 ε
    _∷_ : ∀ {a as Pa Pas} → P2 Pa → AllAll P2 {as} Pas → AllAll P2 {a ∷ as} (Pa ∷ Pas)

  All× : {A B : Set} → (A → Set) → (B → Set) → (A × B → Set)
  All× P1 P2 (a , b) = P1 a × P2 b

  --AllAny : {A : Set} {P : A → Set} → (P2 : ∀ {a} → P a → Set) → (∀ {as} → Any P as → Set)
  --AllAny P2 (here Pa) = P2 Pa
  --AllAny P2 (there any-Pa) = AllAny P2 any-Pa
  --data AllAny {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → All P as → Set where
  data AllAny {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → Any P as → Set where
    here : ∀ {a as} {Pa : P a} → P2 Pa → AllAny P2 {a ∷ as} (here Pa)
    there : ∀ {a as} {any-Pa} → AllAny P2 {as} any-Pa → AllAny P2 {a ∷ as} (there any-Pa)

  AllΣ : {A : Set} {B : A → Set} → ({a : A} → B a → Set) → Σ A B → Set
  AllΣ P (a ,, b) = P b

  single : ∀ {A} → A → List A
  single a = a ∷ ε

  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  $0 : ∀ {A a0 as} → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as} → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2

  single' : {A : Set} {P : A → Set} {a : A} → P a → All P (single a)
  single' Pa = Pa ∷ ε

  _++'_ : {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
  ε ++' Pys = Pys
  (Px ∷ Pxs) ++' Pys = Px ∷ (Pxs ++' Pys)

  mapAll : {A : Set} {P Q : A → Set} → (∀ {a} → P a → Q a) → (∀ {as} → All P as → All Q as)
  mapAll f ε = ε
  mapAll f (Pa ∷ Pas) = f Pa ∷ mapAll f Pas

  mapAny : {A : Set} {P Q : A → Set} → (∀ {a} → P a → Q a) → (∀ {as} → Any P as → Any Q as)
  mapAny f (here Pa) = here (f Pa)
  mapAny f (there Pas) = there (mapAny f Pas)

  mapAnyAll : {A R : Set} {P : A → Set} {as : List A} → Any P as → All (\a → P a → R) as → R
  mapAnyAll (here Pa) (fa ∷ fas) = fa Pa
  mapAnyAll (there Pas) (fa ∷ fas) = mapAnyAll Pas fas

  --mapAllAny : {A R : Set} {P : A → Set} {as : List A} → All P as → Any (\a → P a → R) as → R
  --mapAllAny (Pa ∷ Pas) (here fa)   = fa Pa
  --mapAllAny (Pa ∷ Pas) (there fas) = mapAllAny Pas fas

  getAllAny : {A R : Set} {P Q : A → Set} → (∀ {a} → P a → Q a → R) → (∀ {as} → All P as → Any Q as → R)
  getAllAny f (Pa ∷ Pas) (here Qa) = f Pa Qa
  getAllAny f (Pa ∷ Pas) (there any-Q) = getAllAny f Pas any-Q

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get all-p any-eq = getAllAny (\{ Pa refl → Pa }) all-p any-eq

  _++2_ : ∀ {A P xs ys Pxs Pys} {P2 : {a : A} → P a → Set} → AllAll P2 {xs} Pxs → AllAll P2 {ys} Pys → AllAll {A} {P} P2 {xs ++ ys} (Pxs ++' Pys)
  ε ++2 Pys = Pys
  (Px ∷ Pxs) ++2 Pys = Px ∷ (Pxs ++2 Pys)

  get2 : ∀ {A P a as Pas} → {P2 : ∀ {a} → P a → Set} → AllAll {A} {P} P2 {as} Pas → (i : Has as a) → P2 (get Pas i)
  get2 (x ∷ x₁) (here refl) = x
  get2 (x ∷ x₁) (there i) = get2 x₁ i

  map× : {A1 B1 A2 B2 : Set} → (A1 → A2) → (B1 → B2) → A1 × B1 → A2 × B2
  map× f g (a , b) = f a , g b

  mapΣ : {A : Set} {B1 B2 : A → Set} → (∀ {a} → B1 a → B2 a) → Σ A B1 → Σ A B2
  mapΣ f (a ,, b) = (a ,, f b)

  identity : {A : Set} → A → A
  identity a = a

-- types
module _ where
  data Type : Set where
    _⇒*_ : List Type → Type → Type
    #Sum : List Type → Type
    #Product : List Type → Type
    #Nat : Type
    #List : Type → Type
    #Tree : Type → Type
    #Conat : Type
    --#Delay : Type → Type
    --#Colist : Type → Type
    #Stream : Type → Type

  infixr 5 _⇒_
  _⇒_ : Type → Type → Type
  σ ⇒ τ = single σ ⇒* τ
  
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

module _ (%Function : List Type → Type → Set) (%Value : Type → Set) where
  data IntrF : Type → Set where
    intrArrow   : ∀ {ρs τ} → %Function ρs τ                                  → IntrF (ρs ⇒* τ)
    intrSum     : ∀ {τs}   → Any %Value τs                                   → IntrF (#Sum τs)
    intrProduct : ∀ {τs}   → All %Value τs                                   → IntrF (#Product τs)
    intrNat     :            %Value (#Maybe #Nat)                            → IntrF  #Nat
    intrList    : ∀ {τ}    → %Value (#Maybe (#Pair τ (#List τ)))             → IntrF (#List τ)
    intrTree    : ∀ {τ}    → %Value (#Either τ (#Pair τ (#Tree τ)))          → IntrF (#Tree τ)
    intrConat   :            Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Maybe ρ))  → IntrF  #Conat
    intrStream  : ∀ {τ}    → Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Pair τ ρ)) → IntrF (#Stream τ)

module _ (%Value : Type → Set) where
  data ElimF : Type → Type → Set where
    elimArrow   : ∀ {ρs τ} → All %Value ρs                                → ElimF (ρs ⇒* τ)     τ
    elimSum     : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs                 → ElimF (#Sum τs)     ϕ
    elimProduct : ∀ {τs ϕ} → Any (\τ → %Value (τ ⇒ ϕ)) τs                 → ElimF (#Product τs) ϕ
    elimNat     : ∀ {ϕ}    → %Value (#Maybe ϕ ⇒ ϕ)                        → ElimF  #Nat         ϕ
    elimList    : ∀ {τ ϕ}  → %Value (#Maybe (#Pair τ ϕ) ⇒ ϕ)              → ElimF (#List τ)     ϕ
    elimTree    : ∀ {τ ϕ}  → %Value (#Either τ (#Pair τ (#Pair ϕ ϕ)) ⇒ ϕ) → ElimF (#Tree τ)     ϕ
    elimConat   :                                                           ElimF  #Conat      (#Maybe #Conat)
    elimStream  : ∀ {τ}                                                   → ElimF (#Stream τ)  (#Pair τ (#Stream τ))

module _ where
  module _
      {%F1 %F2 : List Type → Type → Set} (%mapF : ∀ {ρs τ} → %F1 ρs τ → %F2 ρs τ)
      {%V1 %V2 : Type → Set} (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    where
  
    mapIntrF : ∀ {τ} → IntrF %F1 %V1 τ → IntrF %F2 %V2 τ
    mapIntrF (intrArrow rule)   = intrArrow   (%mapF rule)
    mapIntrF (intrSum rule)     = intrSum     (mapAny %mapV rule)
    mapIntrF (intrProduct rule) = intrProduct (mapAll %mapV rule)
    mapIntrF (intrNat rule)     = intrNat     (%mapV rule)
    mapIntrF (intrList rule)    = intrList    (%mapV rule)
    mapIntrF (intrTree rule)    = intrTree    (%mapV rule)
    mapIntrF (intrConat rule)   = intrConat   (mapΣ (map× %mapV %mapV) rule)
    mapIntrF (intrStream rule)  = intrStream  (mapΣ (map× %mapV %mapV) rule)
  
  module _ {%V1 %V2 : Type → Set} (%mapV : ∀ {τ} → %V1 τ → %V2 τ) where
    mapElimF : ∀ {τ ϕ} → ElimF %V1 τ ϕ → ElimF %V2 τ ϕ
    mapElimF (elimArrow rule)   = elimArrow   (mapAll %mapV rule)
    mapElimF (elimSum rule)     = elimSum     (mapAll %mapV rule)
    mapElimF (elimProduct rule) = elimProduct (mapAny %mapV rule)
    mapElimF (elimNat rule)     = elimNat     (%mapV rule)
    mapElimF (elimList rule)    = elimList    (%mapV rule)
    mapElimF (elimTree rule)    = elimTree    (%mapV rule)
    mapElimF  elimConat         = elimConat
    mapElimF  elimStream        = elimStream

  module _
      {%F : List Type → Type → Set} (%AllF : ∀ {ρs τ} → %F ρs τ → Set)
      {%V : Type → Set} (%AllV : ∀ {τ} → %V τ → Set)
    where
    AllIntrF : ∀ {τ} → IntrF %F %V τ → Set
    AllIntrF (intrArrow rule)   = %AllF rule
    AllIntrF (intrSum rule)     = AllAny %AllV rule
    AllIntrF (intrProduct rule) = AllAll %AllV rule
    AllIntrF (intrNat rule)     = %AllV rule
    AllIntrF (intrList rule)    = %AllV rule
    AllIntrF (intrTree rule)    = %AllV rule
    AllIntrF (intrConat rule)   = AllΣ (All× %AllV %AllV) rule
    AllIntrF (intrStream rule)  = AllΣ (All× %AllV %AllV) rule

  module _ {%V : Type → Set} (%AllV : ∀ {τ} → %V τ → Set) where
    AllElimF : ∀ {τ ϕ} → ElimF %V τ ϕ → Set
    AllElimF (elimArrow rule)   = AllAll %AllV rule
    AllElimF (elimSum rule)     = AllAll %AllV rule
    AllElimF (elimProduct rule) = AllAny %AllV rule
    AllElimF (elimNat rule)     = %AllV rule
    AllElimF (elimList rule)    = %AllV rule
    AllElimF (elimTree rule)    = %AllV rule
    AllElimF  elimConat         = ⊤
    AllElimF  elimStream        = ⊤

  allMapAll : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : ∀ {a} → P1 a → Set) → (AllP2 : ∀ {a} → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 P1a → AllP2 (mapP P1a)) → ∀ {as} {P1as : All P1 as} → AllAll AllP1 P1as → AllAll AllP2 (mapAll mapP P1as)
  allMapAll mapP AllP1 AllP2 allMapP ε = ε
  allMapAll mapP AllP1 AllP2 allMapP (allPa ∷ allAllPas) = allMapP allPa ∷ allMapAll mapP AllP1 AllP2 allMapP allAllPas

  allMapAny : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : ∀ {a} → P1 a → Set) → (AllP2 : ∀ {a} → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 P1a → AllP2 (mapP P1a)) → ∀ {as} {any-P1 : Any P1 as} → AllAny AllP1 any-P1 → AllAny AllP2 (mapAny mapP any-P1)
  allMapAny mapP AllP1 AllP2 allMapP (here z) = here (allMapP z)
  allMapAny mapP AllP1 AllP2 allMapP (there z) = there (allMapAny mapP AllP1 AllP2 allMapP z)

  module _
      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ {τ} → %V1 τ → Set)
      (%AllV2 : ∀ {τ} → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 v1 → %AllV2 (%mapV v1))
    where
    allMapElimF : ∀ {τ ϕ} → (elim1 : ElimF %V1 τ ϕ) → AllElimF %AllV1 elim1 → AllElimF %AllV2 (mapElimF %mapV elim1)
    allMapElimF (elimArrow rule)   all = allMapAll %mapV %AllV1 %AllV2 %allMapV all
    allMapElimF (elimSum rule)     all = allMapAll %mapV %AllV1 %AllV2 %allMapV all 
    allMapElimF (elimProduct rule) all = allMapAny %mapV %AllV1 %AllV2 %allMapV all 
    allMapElimF (elimNat rule)     all = %allMapV all 
    allMapElimF (elimList rule)    all = %allMapV all 
    allMapElimF (elimTree rule)    all = %allMapV all 
    allMapElimF  elimConat         all = all
    allMapElimF  elimStream        all = all

module _ (%F : List Type → Type → Set) (%V : Type → Set) where
  data ExprF (τ : Type) : Set where
    intr : IntrF %F %V τ → ExprF τ
    elim : ∀ {ρ} → %V ρ → ElimF %V ρ τ → ExprF τ

-- regular de-bruijn term
data Term (Γ : List Type) (τ : Type) : Set where
  var  : Has Γ τ → Term Γ τ
  wrap : ExprF (\σs τ → Term (σs ++ Γ) τ) (\τ → Term Γ τ) τ → Term Γ τ

-- compiled representation
module _ where
  --mutual
  --  Intr : List Type → Type → Set
  --  Intr Γ τ = IntrF (\ϕs ϕ → TermM (ϕs ++ Γ) ϕ) (Has Γ) τ

  --  Elim : List Type → Type → Type → Set
  --  Elim Γ τ ϕ = ElimF (Has Γ) τ ϕ

  mutual
    Intr : List Type → Type → Set
    Intr Γ τ = IntrF (\ϕs ϕ → TermM (ϕs ++ Γ) ϕ) (Has Γ) τ

    Elim : List Type → Type → Type → Set
    Elim Γ τ ϕ = ElimF (Has Γ) τ ϕ

    --data Expr (Γ : List Type) (τ : Type) : Set where
    --  intr : Intr Γ τ → Expr Γ τ
    --  elim : ∀ {ρ} → Has Γ ρ → Elim Γ ρ τ → Expr Γ τ
    ExprM : List Type → Type → Set
    ExprM Γ τ = ExprF (\ϕs ϕ → TermM (ϕs ++ Γ) ϕ) (Has Γ) τ
  
    --data TermM (Γ : List Type) (τ : Type) : Set where
    --  return : Has Γ τ → TermM Γ τ
    --  set    : ∀ ρ → Expr Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
    data TermM (Γ : List Type) (τ : Type) : Set where
      return : Has Γ τ → TermM Γ τ
      set    : ∀ ρ → ExprM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ

  infixr 5 _▸_
  _▸_ : ∀ {Γ ρ τ} → ExprM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  _▸_ = set _

  compile : ∀ {τ} → Term ε τ → TermM ε τ
  compile = {!!}

-- run-time representation
module _ where
  mutual
    ValueU : Type → Set
    ValueU τ = IntrF Closure Value τ

    data Value (τ : Type) : Set where
      wrap : ValueU τ → Value τ
  
    data Closure (ρs : List Type) (τ : Type) : Set where
      _&_ : ∀ {Γ} → Env Γ → TermM (ρs ++ Γ) τ → Closure ρs τ

    Env : List Type → Set
    Env Γ = All Value Γ

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

  pure : ∀ {Γ τ} → ExprM Γ τ → TermM Γ τ
  pure expr = set _ expr (return $0)

  --apply* : ∀ {ρs τ} → Value (ρs ⇒* τ) → All Value ρs → Closure ε τ
  --apply* {ρs} {τ} function values = (function ∷ values) & (elim (ρs ⇒* τ) τ $0 (refl , {!!}) ▸ return $0)

  apply : ∀ {ρ τ} → Value (ρ ⇒ τ) → Value ρ → Closure ε τ
  --apply function value = apply* function (value ∷ ε)
  apply {ρ} {τ} function value = (function ∷ value ∷ ε) & (elim $0 (elimArrow ($1 ∷ ε)) ▸ return $0)

  {-
  apply' : ∀ {ρs σ τ} → Value (σ ⇒ τ) → Value (ρs ⇒* σ) → Value (ρs ⇒* τ)
  apply' = {!!}

  infixl 10 _^_
  _^_ = apply'

  --compose : ∀ {ρ σ τ} → Value ((σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ (ρ ⇒ τ))
  compose : ∀ {ρ σ τ} → Value (((σ ⇒ τ) ∷ (ρ ⇒ σ) ∷ ρ ∷ ε) ⇒* τ)
  compose = {!!}

  mapMaybe : ∀ {σ τ} → Value (σ ⇒ τ) → Value (#Maybe σ ⇒ #Maybe τ)
  mapMaybe = {!!}

  elimNat : ∀ {ϕ} → Value (#Maybe ϕ ⇒ ϕ) → Value (#Nat ⇒ ϕ)
  elimNat = {!!}

  fromValue : ∀ {τ} → Value (ε ⇒* τ) → Closure ε τ
  fromValue (wrap closure) = closure
  -}

  elimNatClosure : ∀ {ϕ} → Closure (#Maybe #Nat ∷ (#Maybe ϕ ⇒ ϕ) ∷ ε) ϕ
  elimNatClosure = {!!}

  stepElimF : ∀ τ ϕ → Value τ → ElimF Value τ ϕ → Closure ε ϕ
  stepElimF (ρs ⇒* τ) .τ (wrap (intrArrow closure)) (elimArrow values) = applyClosure closure values
  stepElimF (#Sum τs) ϕ (wrap (intrSum any-value)) (elimSum functions) = getAllAny (\function value → apply function value) functions any-value
  stepElimF (#Product τs) ϕ (wrap (intrProduct values)) (elimProduct any-function) = getAllAny (\value function → apply function value) values any-function
  --stepElimF #Nat ϕ (wrap value) step = apply {!compose ^ mapMaybe (elimNat step) ^ step!} value
  stepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) = applyClosure elimNatClosure (value ∷ step ∷ ε)
  stepElimF _ ϕ value rule = {!!}

  stepElim : ∀ {Γ} τ ϕ → Env Γ → Has Γ τ → Elim Γ τ ϕ → Closure ε ϕ
  stepElim τ ϕ env x rule = stepElimF τ ϕ (get env x) (mapElimF (\x → get env x) {τ} rule)

  stepIntr : ∀ {Γ} τ → Env Γ → Intr Γ τ → Value τ
  stepIntr τ env rule = wrap (mapIntrF (\term → env & term) (\x → get env x) {τ} rule)

  step : ∀ {τ} → Machine τ → Step τ
  step ((env & return x) ∷ ε) = finish (get env x)
  step ((env & return x) ∷ (env' & term) ∷ stack) = continue (((get env x ∷ env') & term) ∷ stack)
  step ((env & (set τ (intr rule) cont)) ∷ stack) = continue (((value ∷ env) & cont) ∷ stack)
    where
      value : Value τ
      value = stepIntr τ env rule
  step ((env & (set ϕ (elim x rule) cont)) ∷ stack) = continue ((closure ∷ (env & cont) ∷ stack))
    where
      closure : Closure ε ϕ
      closure = stepElim _ ϕ env x rule

-- run
module _ where
  Pred : Set → Set₁
  Pred A = A → Set

  Pred2 : {A : Set} → (A → Set) → (A → Set₁)
  Pred2 P a = Pred (P a)

  AllPred : {A : Set} {P : A → Set} → ∀ {as} → All₁ (\a → Pred (P a)) as → Pred (All P as)
  AllPred ε ε = ⊤
  AllPred (P2a ∷ P2as) (Pa ∷ Pas) = P2a Pa × AllPred P2as Pas

  AnyPred : {A : Set} {P : A → Set} → ∀ {as} → All₁ (\a → Pred (P a)) as → Pred (Any P as)
  AnyPred (P2a ∷ P2as) (here Pa) = P2a Pa
  AnyPred (P2a ∷ P2as) (there Pas) = AnyPred P2as Pas

  Val : Type → Set₁
  Val τ = Pred (Value τ)

  AllVal : List Type → Set₁
  AllVal τs = All₁ Val τs

  data TraceStepF {τ} (%GoodValue : Val τ) : Step τ → Set where
    goodFinish : {value : Value τ} → %GoodValue value → TraceStepF %GoodValue (finish value)
    goodContinue : {machine : Machine τ} → TraceStepF %GoodValue (step machine) → TraceStepF %GoodValue (continue machine)

  TraceClosureF : ∀ {τ} → (%Good-τ : Val τ) → Closure ε τ → Set
  TraceClosureF {τ} %Good-τ closure = TraceStepF %Good-τ (continue (closure ∷ ε))

  -- good types
  module _ where
    AllGoodF : ∀ {τs} → All₁ Val τs → All Value τs → Set
    --AllGoodF {ε} ε ε = ⊤
    --AllGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (value ∷ values) = Good-τ value × AllGoodF Good-τs values
    AllGoodF = AllPred

    AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set
    --AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (here value) = Good-τ value
    --AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (there any-value) = AnyGoodF Good-τs any-value
    AnyGoodF = AnyPred
    --data AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set where
    --  here : ∀ {τ τs} {Good-τ : Val τ} {Good-τs : All₁ Val τs} {value} → Good-τ value → AnyGoodF (Good-τ ∷ Good-τs) (here value)
    --  there : ∀ {τ τs} {Good-τ Good-τs any-value} → AnyGoodF {τs} Good-τs any-value → AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (there any-value)

    Good-⇒ : ∀ {ρs τ} → AllVal ρs → Val τ → Val (ρs ⇒* τ)
    Good-⇒ {ρs} {τ} Good-ρs Good-τ (wrap (intrArrow closure)) = {values : All Value ρs} → AllGoodF Good-ρs values → TraceClosureF Good-τ (applyClosure closure values)

    Good-Sum : ∀ {τs} → AllVal τs → Val (#Sum τs)
    Good-Sum Good-τs (wrap (intrSum any-value)) = AnyGoodF Good-τs any-value

    Good-Product : ∀ {τs} → AllVal τs → Val (#Product τs)
    Good-Product Good-τs (wrap (intrProduct values)) = AllGoodF Good-τs values

    Good-Void : Val #Void
    Good-Void = Good-Sum ε
    
    Good-Unit : Val #Unit
    Good-Unit = Good-Product ε
    
    Good-Either : ∀ {σ τ} → Val σ → Val τ → Val (#Either σ τ)
    Good-Either Good-σ Good-τ = Good-Sum (Good-σ ∷ Good-τ ∷ ε)
    
    Good-Pair : ∀ {σ τ} → Val σ → Val τ → Val (#Pair σ τ)
    --Good-Pair Good-σ Good-τ = Good-Product (Good-σ ∷ Good-τ ∷ ε)
    Good-Pair Good-σ Good-τ (wrap (intrProduct (value1 ∷ value2 ∷ ε))) = Good-σ value1 × Good-τ value2 × ⊤
    
    Good-Maybe : ∀ {τ} → Val τ → Val (#Maybe τ)
    --Good-Maybe Good-τ = Good-Sum (Good-Unit ∷ Good-τ ∷ ε)
    Good-Maybe Good-τ (wrap (intrSum (here unit))) = ⊤
    Good-Maybe Good-τ (wrap (intrSum (there (here value)))) = Good-τ value

    #inl : ∀ {σ τ} → Value σ → Value (#Either σ τ)
    #inl value = wrap (intrSum (here value))

    #inr : ∀ {σ τ} → Value τ → Value (#Either σ τ)
    #inr value = wrap (intrSum (there (here value)))

    #unit : Value #Unit
    #unit = wrap (intrProduct ε)

    #pair : ∀ {σ τ} → Value σ → Value τ → Value (#Pair σ τ)
    #pair value1 value2 = wrap (intrProduct (value1 ∷ value2 ∷ ε))

    #zero : Value #Nat
    #zero = wrap (intrNat (#inl #unit))
  
    #succ : Value #Nat → Value #Nat
    #succ n = wrap (intrNat (#inr n))
  
    #nil : ∀ {τ} → Value (#List τ)
    #nil = wrap (intrList (#inl #unit))
  
    #cons : ∀ {τ} → Value τ → Value (#List τ) → Value (#List τ)
    #cons head tail = wrap (intrList (#inr (#pair head tail)))
  
    data Good-Nat : Value #Nat → Set where
      zero : Good-Nat #zero
      succ : {n : Value #Nat} → Good-Nat n → Good-Nat (#succ n)
  
    data Good-List {τ} (%Good-τ : Value τ → Set) : Value (#List τ) → Set where
      nil : Good-List %Good-τ #nil
      cons : {v : Value τ} {l : Value (#List τ)} → %Good-τ v → Good-List %Good-τ l → Good-List %Good-τ (#cons v l)

    {-
    module _ where
      record Good-Conat' {ρ} (step : Value (ρ ⇒ #Maybe ρ)) (value : Value ρ) : Set where
        coinductive
        --field force : TraceClosureF (Good-Maybe (Good-Conat' step)) (applyClosure step (single' value))
        field force : TraceClosureF (Good-Maybe (Good-Conat' step)) {!!}

      Good-Conat : Val #Conat
      Good-Conat (wrap (ρ ,, value , closure)) = Good-Conat' closure value
      -}

  mutual
    GoodValue : ∀ {τ} → Val τ
    GoodValue {ρs ⇒* τ} = Good-⇒ (AllGoodValue {ρs}) (GoodValue {τ})
    GoodValue {#Sum τs} = Good-Sum (AllGoodValue {τs})
    GoodValue {#Product τs} = Good-Product (AllGoodValue {τs})
    GoodValue {#Nat} = Good-Nat
    --GoodValue {#List τ} = Good-List (GoodValue {τ})
    --GoodValue {#Conat} = Good-Conat
    --GoodValue {#Stream τ} = Good-Stream (GoodValue {τ})
    GoodValue _ = {!!}

    AllGoodValue : ∀ {τs} → AllVal τs
    AllGoodValue {ε} = ε
    AllGoodValue {τ ∷ τs} = GoodValue {τ} ∷ AllGoodValue {τs}

  TraceStep : ∀ {τ} → Step τ → Set
  TraceStep = TraceStepF GoodValue

  Trace : ∀ {τ} → Machine τ → Set
  Trace machine = TraceStep (continue machine)

  {-
  TraceStack : ∀ {ρs τ} → CallStack ρs τ → Set
  TraceStack {ρs} {τ} stack = {env : Env ρs} → AllAll GoodValue env → TraceStep (composeEnvStack env stack)
  -}

  TraceClosureε : ∀ {τ} → Closure ε τ → Set
  TraceClosureε {τ} closure = Trace (closure ∷ ε)

  TraceClosure : ∀ {ρs τ} → Closure ρs τ → Set
  TraceClosure {ρs} {τ} closure = {env : Env ρs} → AllAll GoodValue env → Trace (applyClosure closure env ∷ ε)

  TraceTermM : ∀ {ρs τ} → TermM ρs τ → Set
  TraceTermM {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → Trace ((env & term) ∷ ε)

  --Trace : ∀ {ρs τ} → TermM ρs τ → Set
  --Trace = TraceTermM

  data AllTraceStack : ∀ {ρs τ} → CallStack ρs τ → Set where
    ε : ∀ {τ} → AllTraceStack {single τ} {τ} ε
    _∷_ :
      ∀ {ρs σ τ} {closure : Closure ρs σ} {stack : CallStack (single σ) τ}
      → TraceClosure closure → AllTraceStack stack → AllTraceStack (closure ∷ stack)

  consTrace : ∀ {σ τ} → {closure : Closure ε σ} → {closure' : Closure (single σ) τ} → TraceClosureε closure → TraceClosure closure' → Trace (closure ∷ closure' ∷ ε)
  consTrace = {!!}

  GoodEnv : ∀ {Γ} → Env Γ → Set
  GoodEnv env = AllAll GoodValue env

  allGoodValue : ∀ τ → (rule : IntrF Closure Value τ) → AllIntrF TraceClosure GoodValue {τ} rule → GoodValue {τ} (wrap rule)
  allGoodValue (σs ⇒* τ) closure trace-closure = {!!}
  allGoodValue (#Sum τs) rule all-good = {!!}
  allGoodValue (#Product τs) rule all-good = {!!}
  allGoodValue #Nat rule all-good = {!!}
  allGoodValue _ rule all-good = {!!}
  --allGoodValue (#List τ) rule all-good = {!!}
  --allGoodValue (#Tree τ) rule all-good = {!!}
  --allGoodValue #Conat rule all-good = {!!}
  --allGoodValue (#Stream τ) rule all-good = {!!}

  goodStepIntr :
    ∀ {Γ} τ {env : Env Γ} → GoodEnv env → (rule : Intr Γ τ) → AllIntrF TraceTermM (\_ → ⊤) rule
    → GoodValue (stepIntr τ env rule)
  goodStepIntr τ good-env rule all-intr-good-term = allGoodValue τ _ {!!}

  goodStepElim : ∀ {Γ} τ ϕ {env : Env Γ} → GoodEnv env → (x : Has Γ τ) → (rule : Elim Γ τ ϕ) → TraceClosureε (stepElim τ ϕ env x rule)
  goodStepElim τ ϕ good-env x rule = {!!}

  mutual
    allIntrGoodTerm : ∀ {Γ τ} → (rule : Intr Γ τ) → AllIntrF TraceTermM (\_ → ⊤) rule
    allIntrGoodTerm (intrArrow term)   = traceTermM term
    allIntrGoodTerm (intrSum rule)     = {!!}
    allIntrGoodTerm (intrProduct rule) = {!buildAllAll (\_ → tt) rule!}
    allIntrGoodTerm (intrNat rule)     = tt
    allIntrGoodTerm (intrList rule)    = tt
    allIntrGoodTerm (intrTree rule)    = tt
    allIntrGoodTerm (intrConat rule)   = tt , tt
    allIntrGoodTerm (intrStream rule)  = tt , tt

    traceTermM : ∀ {Γ τ} → (term : TermM Γ τ) → TraceTermM term
    traceTermM (return x) good-env = goodContinue (goodFinish (get2 good-env x))
    traceTermM (set τ (intr rule) term) good-env = goodContinue (traceTermM term (goodStepIntr τ good-env rule (allIntrGoodTerm rule) ∷ good-env))
    traceTermM (set ϕ (elim x rule) term) good-env = goodContinue (consTrace trace-closure \{ (good-value ∷ ε) → trace-term (good-value ∷ good-env) })
      where
        trace-closure : TraceClosureε _
        trace-closure = goodStepElim _ ϕ good-env x rule

        trace-term : TraceTermM term
        trace-term = traceTermM term

  {-
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
    traceClosure (env & return x) good-env' = goodContinue (goodFinish {!!})
    traceClosure (env & set ρ (intr .ρ x) term) good-env' = goodContinue (goodContinue {!!})
    traceClosure (env & set ρ (elim τ .ρ x x₁) term) good-env' = goodContinue (goodContinue {!traceClosure (env & term)!})
    -}

  run : ∀ {τ} → (machine : Machine τ) → Trace machine
  run (closure ∷ machine) = {!traceClosure closure!}

  result : ∀ {τ} {machine : Machine τ} → Trace machine → Value τ
  result trace = resultStep trace where
    resultStep : ∀ {τ} {step : Step τ} → TraceStep step → Value τ
    resultStep (goodFinish {value} _good-value) = value
    resultStep (goodContinue trace) = resultStep trace

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))
