module _ where

module _ where
  data Bool : Set where
    false true : Bool
  {-# BUILTIN BOOL Bool #-}
  {-# BUILTIN FALSE false #-}
  {-# BUILTIN TRUE true #-}

  if : {A : Set} → Bool → A → A → A
  if true x y = x
  if false x y = y
    
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

  maybe : {A B : Set} → Maybe A → B → (A → B) → B
  maybe nothing b f = b
  maybe (just a) b f = f a

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  single : {A : Set} → A → List A
  single a = a ∷ ε

  postulate String : Set
  {-# BUILTIN STRING String #-}

  primitive primStringEquality : String → String → Bool

data Var : Set where
  v : String → Var

eqVar : Var → Var → Bool
eqVar (v x) (v y) = primStringEquality x y

data Term : Set where
  var : (x : Var) → Term
  set : Term
  arr : (A : Term) → (z : Var) → (B : Term) → Term
  abs : (A : Term) → (z : Var) → (B : Term) → (x : Var) → (M : Term) → Term
  app : (A : Term) → (z : Var) → (B : Term) → (M : Term) → (N : Term) → Term

subst : Term → Var → Term → Term
subst = {!!}

Context : Set
Context = List (Var × Term)

lookup : List (Var × Term) → Var → Maybe Term
lookup ε x = nothing
lookup ((x' , A) ∷ Γ) x = if (eqVar x' x) (just A) (lookup Γ x) 

data Rule : Set where
  #check : Context → Term → Term → Rule
  #has : Context → Var → Term → Rule
  #eq : Term → Term → Rule
  #fail : Rule → Rule

check : Context → Term → Term → List Rule
check Γ C (var x) = #has Γ x C ∷ ε
check Γ C set = #eq C set ∷ ε
check Γ C (arr A z B) = #check Γ set A ∷ #check (z , A ∷ Γ) set B ∷ ε
check Γ C (abs A z B x M) = #check Γ set A ∷ #check (z , A ∷ Γ) set B ∷ #check ((x , A) ∷ Γ) B M ∷ #eq C (arr A z B) ∷ ε
check Γ C (app A z B M N) = #check Γ set A ∷ #check (z , A ∷ Γ) set B ∷ #check Γ (arr A z B) M ∷ #check Γ A M ∷ #eq C (subst B z N) ∷ ε

_++_ : {A : Set} → List A → List A → List A
ε ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concatMap : {A : Set} → (A → List A) → (List A → List A)
concatMap f ε = ε
concatMap f (a ∷ as) = f a ++ concatMap f as

step : List Rule → List Rule
step = concatMap step'
  where
    step' : Rule → List Rule
    step' (#check Γ C M) = check Γ C M
    step' r@(#has Γ x A) = maybe (lookup Γ x) (single (#fail r)) (\A' → single (#eq A A'))
    step' other = single other

run : ℕ → Rule → List Rule
run n r = run' n (single r)
  where
    run' : ℕ → List Rule → List Rule
    run' zero rs = rs
    run' (succ n) rs = run' n (step rs)

$idT : Term
$idT = arr set A (arr $A # $A)
  where
    # = v "_"
    A = v "A"
    $A = var A

$id : Term
$id = abs set A (arr $A # $A) A (abs $A # $A a ($a))
  where
    # = v "_"
    A = v "A"
    $A = var A
    a = v "a"
    $a = var a

_ : {!!}
_ = {!run 5 (#check ε $idT $id)!}
