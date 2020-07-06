module _ where

module _ where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

data Lv : Set where
  L0 : Lv
  L1 : Lv

mutual
  data Type : Lv → Set where
    #Tvar : Type L1
    _⇒_ : ∀ {l} → Type l → Type l → Type l
    #Nat : ∀ {l} → Type l
    #Maybe : ∀ {l} → Type l → Type l
    #Forall : Type L1 → Type L0
    #Exists : Type L1 → Type L0
    #Ap : ∀ {l₁ l₂} → Type l₁ → TypeEnv' l₁ l₂ → Type l₂

  data TypeEnv' : (l₁ l₂ : Lv) → Set where
    mkTypeEnv0 : ∀ {l} → TypeEnv' L0 l
    mkTypeEnv1 : ∀ {l} → Type l → TypeEnv' L1 l

↑_ : Type L0 → Type L1
↑ τ₀ = #Ap τ₀ mkTypeEnv0

_%_ : Type L1 → Type L0 → Type L0
τ₁ % τ₀ = #Ap τ₁ (mkTypeEnv1 τ₀)

data TypeValue : Set where
  _⇒_ : TypeValue → TypeValue → TypeValue
  #Nat : TypeValue
  #Maybe : TypeValue → TypeValue
  #Forall : Type L1 → TypeValue
  #Exists : Type L1 → TypeValue

{-
data TypeEnv : (l : Lv) → Set where
  mkTypeEnv0 : TypeEnv L0
  mkTypeEnv1 : Type L0 → TypeEnv L1
  -}
TypeEnv : Lv → Set
TypeEnv l = TypeEnv' l L0
  
data TypeThunk : Set where
  mkTypeThunk : (l : Lv) → TypeEnv l → Type l → TypeThunk

{-
ap : ∀ {l} → Type l → TypeEnv l → Type L0
ap (τ ⇒ τ') e = ap τ e ⇒ ap τ' e
ap #Nat e = #Nat
ap (#Maybe τ) e = #Maybe (ap τ e)
ap (↑ τ) e = τ
ap #Tvar (mkTypeEnv1 δ) = δ
ap (#Forall τ) e = #Forall τ
ap (#Exists τ) e = #Exists τ
ap (τ % τ₁) e = τ % τ₁
-}


data Context : Lv → Set where
  ε : Context L0
  _∷_ : ∀ {l} → Type l → Context l → Context l
  ∗∷_ : Context L0 → Context L1


data Var : ∀ l → Context l → Type l → Set where
  mkVar : {!!} → Var {!!} {!!} {!!}

data Term : (l : Lv) → Context l → Type l → Set where
  var : ∀ {l Γ τ} → Var l Γ τ → Term l Γ τ

  ⇒-intr : ∀ {l Γ} → ∀ ρ τ → Term l (ρ ∷ Γ) τ → Term l Γ (ρ ⇒ τ)
  ⇒-elim : ∀ {l Γ ρ τ} → Term l Γ ρ → Term l Γ (ρ ⇒ τ) → Term l Γ τ

  Maybe-intr : ∀ {l Γ τ} → Maybe (Term l Γ τ) → Term l Γ (#Maybe τ)
  Maybe-elim : ∀ {l Γ τ} ϕ → Term l Γ ϕ → Term l Γ (τ ⇒ ϕ) → Term l Γ (#Maybe τ) → Term l Γ ϕ

  Nat-intr : ∀ {l Γ} → Term l Γ (#Maybe #Nat) → Term l Γ #Nat
  Nat-elim : ∀ {l Γ} ϕ → Term l Γ (#Maybe ϕ ⇒ ϕ) → Term l Γ #Nat → Term l Γ ϕ

  ∀-intr : ∀ {Γ τ₁} → Term L1 (∗∷ Γ) τ₁ → Term L0 Γ (#Forall τ₁)
  ∀-elim : ∀ {Γ τ₁} ϕ₀ → Term L0 Γ (#Forall τ₁) → Term L0 Γ (τ₁ % ϕ₀)

  ∃-intr : ∀ {Γ ϕ₀ τ₁} → Term L0 Γ (τ₁ % ϕ₀) → Term L0 Γ (#Exists τ₁)
  ∃-elim : ∀ {Γ ϕ₀ τ₁} → Term L0 Γ (#Forall (τ₁ ⇒ (↑ ϕ₀))) → Term L0 Γ (#Exists τ₁) → Term L0 Γ ϕ₀

mutual
  data TermC : (l : Lv) → Context l → Type l → Set where
    ret : ∀ {l Γ τ} → Var l Γ τ → TermC l Γ τ
    set : ∀ {l Γ ρ τ} → ExprC l Γ ρ → TermC l (ρ ∷ Γ) τ → TermC l Γ τ

  data ExprC : (l : Lv) → Context l → Type l → Set where
    ⇒-intr : ∀ {l Γ} ρ τ → TermC l (ρ ∷ Γ) τ → ExprC l Γ (ρ ⇒ τ)
    ⇒-elim : ∀ {l Γ ρ τ} → Var l Γ ρ → Var l Γ (ρ ⇒ τ) → ExprC l Γ τ
  
    Maybe-intr : ∀ {l Γ τ} → Maybe (Var l Γ τ) → ExprC l Γ (#Maybe τ)
    Maybe-elim : ∀ {l Γ τ} ϕ → Var l Γ ϕ → Var l Γ (τ ⇒ ϕ) → Var l Γ (#Maybe τ) → ExprC l Γ ϕ
  
    Nat-intr : ∀ {l Γ} → Var l Γ (#Maybe #Nat) → ExprC l Γ #Nat
    Nat-elim : ∀ {l Γ} ϕ → Var l Γ (#Maybe ϕ ⇒ ϕ) → Var l Γ #Nat → ExprC l Γ ϕ
  
    ∀-intr : ∀ {Γ} → ∀ τ₁ → TermC L1 (∗∷ Γ) τ₁ → ExprC L0 Γ (#Forall τ₁)
    ∀-elim : ∀ {Γ τ₁} ϕ₀ → Var L0 Γ (#Forall τ₁) → ExprC L0 Γ (τ₁ % ϕ₀)
  
    ∃-intr : ∀ {Γ τ₁} → ∀ ϕ₀ → Var L0 Γ (τ₁ % ϕ₀) → ExprC L0 Γ (#Exists τ₁)
    ∃-elim : ∀ {Γ ϕ₀ τ₁} → Var L0 Γ (#Forall (τ₁ ⇒ (↑ ϕ₀))) → Var L0 Γ (#Exists τ₁) → ExprC L0 Γ ϕ₀

pure : ∀ {l Γ τ} → ExprC l Γ τ → TermC l Γ τ
pure = {!!}

mutual
  data Value : Type L0 → Set where
    ⇒-constr     : ∀ {ρ τ} → Closure ρ τ → Value (ρ ⇒ τ)
    Maybe-constr : ∀ {τ} → Maybe (Value τ) → Value (#Maybe τ)
    Nat-constr   : Value (#Maybe #Nat) → Value #Nat
    ∀-constr     : ∀ {τ₁} → ClosureT τ₁ → Value (#Forall τ₁)
    ∃-constr     : ∀ {τ₁} → ∀ ϕ₀ → Value (τ₁ % ϕ₀) → Value (#Exists τ₁)

  data Env : (l : Lv) → TypeEnv l → Context l → Set where
    ε : Env L0 mkTypeEnv0 ε
    -- _∷_ : ∀ {l τ envT Γ} → Value (ap τ envT) → Env l envT Γ → Env l envT (τ ∷ Γ)
    _∷_ : ∀ {l τ envT Γ} → Value {!!} → Env l envT Γ → Env l envT (τ ∷ Γ)
    _∗∷_ : ∀ {Γ} → (δ : Type L0) → Env L0 mkTypeEnv0 Γ → Env L1 (mkTypeEnv1 δ) (∗∷ Γ)

  data Closure : Type L0 → Type L0 → Set where
    -- mkClosure : ∀ {l Γ} → ∀ ρ τ → (envT : TypeEnv l) → Env l envT Γ → TermC l (ρ ∷ Γ) τ → Closure (ap ρ envT) (ap τ envT)
    mkClosure : ∀ {l Γ} → ∀ ρ τ → (envT : TypeEnv l) → Env l envT Γ → TermC l (ρ ∷ Γ) τ → Closure {!!} {!!}

  data ClosureT : Type L1 → Set where
    mkClosureT : ∀ {Γ} → ∀ τ → (envT : TypeEnv L0) → Env L0 envT Γ → TermC L1 (∗∷ Γ) τ → ClosureT τ

data Thunk : TypeThunk → Set where
  mkThunk : ∀ l Γ τ → (envT : TypeEnv l) → Env l envT Γ → TermC l Γ τ → Thunk (mkTypeThunk l envT τ)

-- get : ∀ {l Γ τ} → (envT : TypeEnv l) → Env l envT Γ → Var l Γ τ → Value (ap τ envT)
get : ∀ {l Γ τ} → (envT : TypeEnv l) → Env l envT Γ → Var l Γ τ → Value {!!}
get = {!!}

data ExprR : Type L0 → Set where
  ⇒-intr : ∀ ρ τ → Closure ρ τ → ExprR (ρ ⇒ τ)
  ⇒-elim : ∀ {ρ τ} → Value ρ → Value (ρ ⇒ τ) → ExprR τ

  Maybe-intr : ∀ {τ} → Maybe (Value τ) → ExprR (#Maybe τ)
  Maybe-elim : ∀ {τ} ϕ → Value ϕ → Value (τ ⇒ ϕ) → Value (#Maybe τ) → ExprR ϕ

  Nat-intr : Value (#Maybe #Nat) → ExprR #Nat
  Nat-elim : ∀ ϕ → Value (#Maybe ϕ ⇒ ϕ) → Value #Nat → ExprR ϕ

  ∀-intr : ∀ τ₁ → ClosureT τ₁ → ExprR (#Forall τ₁)
  ∀-elim : ∀ {τ₁} ϕ₀ → Value (#Forall τ₁) → ExprR (τ₁ % ϕ₀)

  ∃-intr : ∀ {τ₁} → ∀ ϕ₀ → Value (τ₁ % ϕ₀) → ExprR (#Exists τ₁)
  ∃-elim : ∀ {ϕ₀ τ₁} → Value (#Forall (τ₁ ⇒ (↑ ϕ₀))) → Value (#Exists τ₁) → ExprR ϕ₀

-- reduce : Env l Γ, Expr l Γ τ₀ → Value τ₀ + Thunk τ₀
plugEnv : ∀ {l Γ τ} → (envT : TypeEnv l) → Env l envT Γ → ExprC l Γ τ → ExprR {!!}
plugEnv = {!!}
{-
plugEnv : ∀ {l Γ τ} → (envT : TypeEnv l) → Env l envT Γ → ExprC l Γ τ → ExprR (ap τ envT)
plugEnv envT env (⇒-intr ρ τ term) = ⇒-intr (ap ρ envT) (ap τ envT) (mkClosure ρ τ envT env term)
plugEnv envT env (Maybe-intr nothing) = Maybe-intr nothing
plugEnv envT env (Maybe-intr (just x)) = Maybe-intr (just (get envT env x))
plugEnv envT env (Nat-intr x) = Nat-intr (get envT env x)
plugEnv envT env (∀-intr τ₁ term) = ∀-intr τ₁ (mkClosureT τ₁ envT env term)
plugEnv envT env (∃-intr ϕ₀ x) = ∃-intr ϕ₀ (get envT env x)
plugEnv envT env (⇒-elim x x₁) = ⇒-elim (get envT env x) (get envT env x₁)
plugEnv envT env (Maybe-elim ϕ x x₁ x₂) = Maybe-elim (ap ϕ envT) (get envT env x) (get envT env x₁) (get envT env x₂)
plugEnv envT env (Nat-elim ϕ x x₁) = Nat-elim (ap ϕ envT) (get envT env x) (get envT env x₁)
plugEnv envT env (∀-elim ϕ₀ x) = ∀-elim ϕ₀ (get envT env x)
plugEnv envT env (∃-elim x x₁) = ∃-elim {!get envT env x!} (get envT env x₁)
-}

infixr 5 _▸_
_▸_ : ∀ {l Γ ρ τ} → ExprC l Γ ρ → TermC l (ρ ∷ Γ) τ → TermC l Γ τ
_▸_ = set

{-
eliminateNat : ∀ {ϕ} → Value (#Maybe ϕ ⇒ ϕ) → Value #Nat → Thunk ϕ
eliminateNat {ϕ} f (Nat-constr v) = {!
     mkThunk L0 (_ ∷ _ ∷ _) ϕ mkEnvT0 (f ∷ v ∷ ε)
     ( Maybe-intr nothing
     ▸ ⇒-intr #Nat (#Maybe ϕ) (Nat-elim _ {!$2!} {!$0!} ▸ pure (Maybe-intr (just {!$0!})))
     ▸ Maybe-elim ϕ {!$1!} {!$0!} {!$3!}
     ▸ pure (⇒-elim {!$3!} {!$0!})
     )
 !}


reduceR : ∀ {τ} → ExprR τ → Value τ + Thunk τ
reduceR (⇒-intr ρ τ closure) = inl (⇒-constr closure)
reduceR (Maybe-intr nothing) = inl (Maybe-constr nothing)
reduceR (Maybe-intr (just x)) = inl (Maybe-constr (just x))
reduceR (Nat-intr x) = inl (Nat-constr x)
reduceR (∀-intr τ₁ closureT) = inl (∀-constr closureT)
reduceR (∃-intr ϕ₀ x) = inl (∃-constr ϕ₀ x)
reduceR (⇒-elim v (⇒-constr (mkClosure ρ τ envT env term))) = inr (mkThunk _ _ τ envT (v ∷ env) term)
reduceR (Maybe-elim ϕ x f (Maybe-constr nothing)) = inr {!mkThunk L0 (_ ∷ ε) ϕ mkEnvT0 (x ∷ ε) (ret {!!})!}
reduceR (Maybe-elim ϕ x f (Maybe-constr (just v))) = inr {!mkThunk L0 (_ ∷ _ ∷ ε) ϕ mkEnvT0 (f ∷ v ∷ ε) (pure (⇒-elim ? ?)) !}
reduceR (Nat-elim ϕ f (Nat-constr n)) = inr {!!}
reduceR (∀-elim ϕ₀ (∀-constr (mkClosureT τ mkEnvT0 env term))) = inr {!mkThunk τ (mkEnvT1 ϕ₀) (ϕ₀ ∗∷ env) term!}
reduceR (∃-elim f (∃-constr ϕ₀ v)) = inr {!!}

reduce : ∀ {l Γ τ} → (envT : EnvT l) → Env l envT Γ → ExprC l Γ τ → Value (ap τ envT) + Thunk (ap τ envT)
reduce envT env expr = reduceR (plugEnv envT env expr)
-}
