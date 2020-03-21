module _ where

module _ where
  data Bool : Set where
    false true : Bool
  {-# BUILTIN BOOL Bool #-}
  {-# BUILTIN FALSE false #-}
  {-# BUILTIN TRUE true #-}

  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  infixr 10 _×_
  infixr 10 _,_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  postulate String : Set
  {-# BUILTIN STRING String #-}

  primitive
    primStringEquality : String → String → Bool

  if : {A : Set} → Bool → A → A → A
  if true a b = a
  if false a b = b

  _=ℕ_ : ℕ → ℕ → Bool
  zero   =ℕ zero   = true
  zero   =ℕ succ _ = false
  succ _ =ℕ zero   = false
  succ n =ℕ succ m = n =ℕ m

  _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>= _ = nothing
  just a >>= f = f a

  _<$>_ : {A B : Set} → (A → B) → (Maybe A → Maybe B)
  f <$> nothing = nothing
  f <$> just a = just (f a)

  _<&>_ : {A B : Set} → Maybe A → (A → B) → Maybe B
  nothing <&> _ = nothing
  just a <&> f = just (f a)

data Type : Set where
  _⇒_ : Type → Type → Type
  Nat : Type

VN : Set
VN = String

Context : Set
Context = List (VN × Type)

data Var : Context → Type → Set where
  here : ∀ {x σ Γ} → Var ((x , σ) ∷ Γ) σ
  there : ∀ {x σ σ' Γ} → Var Γ σ → Var ((x , σ') ∷ Γ) σ

mutual
  data Term (Γ : Context) (τ : Type) : Set where
    var : Var Γ τ → Term Γ τ
    set : (σ : Type) → (x : VN) → Expr Γ σ → Term ((x , σ) ∷ Γ) τ → Term Γ τ
  
  data Expr (Γ : Context) : Type → Set where
    #abs : (σ τ : Type) → (x : VN) → Term ((x , σ) ∷ Γ) τ → Expr Γ (σ ⇒ τ)
    #app : (σ τ : Type) → Var Γ (σ ⇒ τ) → Var Γ σ → Expr Γ τ
    #zero : Expr Γ Nat
    #succ : Var Γ Nat → Expr Γ Nat
    #ind : (ρ : Type) → Var Γ ρ → (x : VN) → Term ((x , ρ) ∷ Γ) ρ → Var Γ Nat → Expr Γ ρ

mutual
  data Value : Type → Set where
    $zero : Value Nat
    $succ : Value Nat → Value Nat
    $abs : (Γ : Context) → (σ τ : Type) → (x : VN) → Term ((x , σ) ∷ Γ) τ → Env Γ → Value τ
    
  data Env : Context → Set where
    ε : Env ε
    _∷_ : ∀ {x σ Γ} → Value σ → Env Γ → Env ((x , σ) ∷ Γ)

-- env
module _ where
  get : ∀ {Γ τ} → Env Γ → Var Γ τ → Value τ
  get (v ∷ γ) here = v
  get (v ∷ γ) (there x) = get γ x

  put : ∀ {Γ σ} → Env Γ → (x : VN) → Value σ → Env ((x , σ) ∷ Γ)
  put γ x v = v ∷ γ

data Cont (σ τ : Type) : Set where
  ∗ : Cont τ τ
  mkCont : (Γ : Context) → (ρ : Type) → (x : VN) → (K : Term ((x , τ) ∷ Γ) ρ) → (γ : Env Γ) → (k : Cont ρ τ) → Cont σ τ

record State (Γ : Context) (τ : Type) : Set where
  constructor s[_,_,_]
  field
    sEnv : Env Γ
    sTerm : Term Γ τ
    sCont : Cont τ

{-
step : State → Maybe (Value + State)
step s[ γ , var a , ∗ ] = inl <$> get γ a
step s[ γ , var a , ( x , K , γ' ) ▹ ks ] = inr <$> (get γ a <&> \v → s[ put γ' x v , K , ks ])
step s[ γ , set x (#abs y M) N , ks ] = inr <$> just s[ put γ x ($abs y M γ) , N , ks ] 
step s[ γ , set x (#app a b) N , ks ] = inr <$> ((get γ a >>= unabs) >>= \{ (y , M , γ') → get γ b <&> \vb → s[ put γ' y vb , M , ( x , N , γ ) ▹ ks ] })
  where
    unabs : Value → Maybe (Var × Term × Env)
    unabs ($abs x M γ) = just (x , M , γ)
    unabs _ = nothing
step s[ γ , set x #zero N , ks ] = inr <$> just s[ put γ x $zero , N , ks ]
step s[ γ , set x (#succ a) N , ks ] = inr <$> (get γ a <&> \va → s[ put γ x ($succ va) , N , ks ])
step s[ γ , set x (#ind a y M b) N , ks ] = inr <$> {!get γ a!}
-}
step : ∀ {Γ τ} → State Γ τ → Value τ + State Γ τ
step s[ γ , var a , ∗ ] = inl (get γ a)
step s[ γ , var a , mkCont Γ ρ x K γ' k ] = inr s[ {!K!} , {!K!} , {!!} ]
step s[ γ , set .(σ ⇒ τ) x (#abs σ τ y M) N , ks ] = {!!}
step s[ γ , set .τ x (#app σ τ a b) N , ks ] = {!!}
step s[ γ , set .Nat x #zero N , ks ] = {!!}
step s[ γ , set .Nat x (#succ a) N , ks ] = {!!}
step s[ γ , set .ρ x (#ind ρ a y M b) N , ks ] = {!!}

{-
ex : Term
ex =
  set "F1" (
    #abs "f" (
    set "Z" #zero (
    set "fZ" (#app "f" "Z") (
    set "ffZ" (#app "f" "fZ") (var "ffZ")
  )))) (
  set "F2" (#abs "x" (set "Sx" (#succ "x") (var "Sx"))) (
  set "F1F2" (#app "F1" "F2") (
  var "F1F2" )))

run : ℕ → Term → Maybe (Value + State)
run n M = run' n (just (inr s[ ε , M , ∗ ]))
  where
    run' : ℕ → Maybe (Value + State) → Maybe (Value + State)
    run' zero s = s
    run' (succ n) nothing = nothing
    run' (succ n) (just (inl v)) = just (inl v)
    run' (succ n) (just (inr s)) = run' n (step s)

_ = {!run 12 ex!}
-}
