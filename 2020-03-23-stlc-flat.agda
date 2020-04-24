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

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

  mapAny : {A : Set} {P Q : A → Set} {as : List A} → ({a : A} → P a → Q a) → Any P as → Any Q as
  mapAny f (here Pa) = here (f Pa)
  mapAny f (there Pas) = there (mapAny f Pas)


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
  #List : Type → Type
  #Conat : Type
  #Colist : Type → Type
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

module _ (%Term : Type → Set) (%Abs : List Type → Type → Set) where
  data TermF : Type → Set where
    lambda : ∀ {ρs τ} → %Abs ρs τ → TermF (ρs ⇒ τ)
    call   : ∀ {ρs τ} → %Term (ρs ⇒ τ) → All %Term ρs → TermF τ

    inj  : ∀ {τs} → Any %Term τs → TermF (#Sum τs)
    case : ∀ {τs ρ} → %Term (#Sum τs) → All (\τ → %Abs (single τ) ρ) τs → TermF ρ

    tuple   : ∀ {τs} → All %Term τs → TermF (#Product τs)
    untuple : ∀ {τs ρ} → %Term (#Product τs) → %Abs τs ρ → TermF ρ

    buildNat : %Term (#Maybe #Nat) → TermF #Nat
    foldNat  : ∀ {ρ} → %Term #Nat → %Abs (single (#Maybe ρ)) ρ → TermF ρ

    buildList : ∀ {τ} → %Term (#Maybe (#Pair τ (#List τ))) → TermF (#List τ)
    foldList  : ∀ {τ ρ} → %Term (#List τ) → %Abs (single (#Maybe (#Pair τ ρ))) ρ → TermF ρ

    buildConat : ∀ {ρ} → %Term ρ → %Abs (single ρ) (#Maybe ρ) → TermF #Conat
    forceConat : %Term #Conat → TermF (#Maybe #Conat)

    buildColist : ∀ {τ ρ} → %Term ρ → %Abs (single ρ) (#Maybe (#Pair τ ρ)) → TermF (#Colist τ)
    forceColist : ∀ {τ} → %Term (#Colist τ) → TermF (#Maybe (#Pair τ (#Colist τ)))

    buildStream : ∀ {τ ρ} → %Term ρ → %Abs (single ρ) (#Pair τ ρ) → TermF (#Stream τ)
    forceStream : ∀ {τ} → %Term (#Stream τ) → TermF (#Pair τ (#Stream τ))

{-
(∀ ρ → %Term ρ → CallStack ε ρ) → TermF %Term _ τ → CallStack ε τ

_ : %Env ε
_ : %Env ρs, %Env τs → %Env (ρs ++ τs)

data Comp ρs τ where
  value : Value τ → Comp ε τ
  ε     : Comp τ τ
  _∷_   : Closure ρs τ → Comp (single τ) ϕ → Comp ρs ϕ

- %V : Type → Set
- apply : Closure ρs τ, All %V ρs → Comp ε τ
Value τ → Elim τ ϕ → Comp ε ϕ
stepExpr : All %V τs → TermF %V Closure τ → Comp ε τ

-}

mutual
  Expr : List Type → Type → Set
  Expr Γ τ = TermF (\ϕ → Has Γ ϕ) (\ρs ϕ → Term (ρs ++ Γ) ϕ) τ
  
  data Term (Γ : List Type) : Type → Set where
    ret : ∀ {τ} → Var Γ τ → Term Γ τ 
    --set : ∀ {ρ ϕ} → Expr Γ ρ → Term (ρ ∷ Γ) ϕ → Term Γ ϕ
    set' : ∀ {ϕ} → TermF (\τ → Term Γ τ) (\ρs τ → Term (ρs ++ Γ) τ) ϕ → Term Γ ϕ

data Term' (Γ : Type → Set) (τ : Type) : Set where
  pure : Γ τ → Term' Γ τ
  roll : TermF (\ϕ → Term' Γ ϕ) (\ρs ϕ → Term' (\σ → Has ρs σ + Γ σ) ϕ) τ → Term' Γ τ

data Stack' (τ : Type) : Set where
  pure : Term' (\_ → ⊥) τ → Stack' τ
  roll : Term' (\ϕ → Stack' ϕ) τ → Stack' τ
-- Stack' ~ Term'

module _ (%Value : Type → Set) (%Closure : List Type → Type → Set) where
  ValueF : Type → Set
  ValueF (ρs ⇒ τ)      = %Closure ρs τ
  ValueF (#Sum τs)     = Any %Value τs
  ValueF (#Product τs) = All %Value τs
  ValueF #Nat          = %Value (#Maybe #Nat)
  ValueF (#List τ)     = %Value (#Maybe (#Pair τ (#List τ)))
  ValueF #Conat        = Σ Type (\ρ → %Value ρ × %Closure (single ρ) (#Maybe ρ))
  ValueF (#Colist τ)   = Σ Type (\ρ → %Value ρ × %Closure (single ρ) (#Maybe (#Pair τ ρ)))
  ValueF (#Stream τ)   = Σ Type (\ρ → %Value ρ × %Closure (single ρ) (#Pair τ ρ))

mutual
  data Value (τ : Type) : Set where
    wrap : ValueF Value Closure τ → Value τ

  data Closure (ρs : List Type) (τ : Type) : Set where
    _&_ : ∀ {τs} → Env τs → Term (ρs ++ τs) τ → Closure ρs τ

  Env : List Type → Set
  Env τs = All Value τs

data CallStack : List Type → Type → Set where
  ε   : ∀ {τ} → CallStack (single τ) τ
  _∷_ : ∀ {ρs τ ϕ} → Closure ρs τ → CallStack (single τ) ϕ → CallStack ρs ϕ

Comp : Type → Set
Comp τ = Value τ + CallStack ε τ

data PrettyTerm (Γ : List Type) (ϕ : Type) : Set where
  wrap : TermF (\τ → PrettyTerm Γ τ) (\ρs τ → PrettyTerm (ρs ++ Γ) τ) ϕ → PrettyTerm Γ ϕ
  --lett : ∀ {ρ} → PrettyTerm Γ ρ → PrettyTerm (ρ ∷ Γ) ϕ → PrettyTerm Γ ϕ

AllValue : List Type → Set
AllValue ε = ⊤
AllValue (τ ∷ τs) = Value τ × AllValue τs

AnyValue : List Type → Set
AnyValue ε = ⊥
AnyValue (τ ∷ τs) = Value τ + AnyValue τs

applyClosure : ∀ {ρs τ} → Closure ρs τ → Env ρs → Closure ε τ
applyClosure (env & term) values = (values ++' env) & term

stepExprF : ∀ {τ} → TermF Value Closure τ → Comp τ
stepExprF (lambda c) = inl (wrap c)
stepExprF (inj x) = inl (wrap x)
stepExprF (tuple xs) = inl (wrap xs)
stepExprF (buildNat f) = inl (wrap f)
stepExprF (buildList f) = inl (wrap f)
stepExprF (buildColist x f) = inl (wrap (_ ,, (x , f)))
stepExprF (buildStream x f) = inl (wrap (_ ,, (x , f)))
stepExprF (buildConat x f) = inl (wrap (_ ,, (x , f)))
stepExprF (call (wrap c) xs) = inr (applyClosure c xs ∷ ε)
stepExprF (case (wrap x) cs) = inr ({!applyClosure !} ∷ ε)
stepExprF (untuple (wrap xs) c) = inr (applyClosure c xs ∷ ε)
stepExprF (foldNat (wrap x) f) = inr {!applyClosure f (x ∷ ε)!}
stepExprF (foldList (wrap x) f) = inr {!applyClosure f (x ∷ ε)!}
stepExprF (forceConat (wrap (ρ ,, (x , f)))) = inr {!applyClosure f (x ∷ ε)!}
stepExprF (forceColist (wrap (ρ ,, (x , f)))) = inr {!applyClosure f (x ∷ ε)!}
stepExprF (forceStream (wrap (ρ ,, (x , f)))) = inr {!applyClosure f (x ∷ ε)!}

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

{-
Term Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ

All (Term Γ) ρs → Term (ρs ++ Γ) ϕ → Term Γ ϕ

-}

stepExpr : ∀ {ρs τ} → Env ρs → Expr ρs τ → Value τ + CallStack ε τ
stepExpr = {!!}

composeStackStack : ∀ {ρs τ ϕ} → CallStack ρs τ → CallStack (single τ) ϕ → CallStack ρs ϕ
composeStackStack ε stack2 = stack2
composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

composeValueStack : ∀ {τ ϕ} → Value τ → CallStack (single τ) ϕ → Comp ϕ
composeValueStack value ε = inl value
composeValueStack value ((env & term) ∷ stack) = inr (((value ∷ env) & term) ∷ stack)

composeCompStack : ∀ {τ ϕ} → Comp τ → CallStack (single τ) ϕ → Comp ϕ
composeCompStack (inl value) stack = composeValueStack value stack
composeCompStack (inr stack') stack = inr (composeStackStack stack' stack)

step : ∀ {τ} → CallStack ε τ → Comp τ
step = {!!}
--step ((env & ret x) ∷ stack) = composeValueStack (get env x) stack
--step ((env & set expr term) ∷ stack) = composeCompStack (stepExpr env expr) ((env & term) ∷ stack)


-- lem-composeSS : composeStackStack (composeStackStack stack1 stack2) stack3 ≡ composeStackStack stack1 (composeStackStack stack2 stack3)
-- lem-composeVS : composeCompStack (composeValueStack value stack1) stack2 ≡ composeValueStack value (composeStackStack stack1 stack2)
-- lem-step : composeCompStack (step stack1) stack2 ≡ step (composeStackStack stack1 stack2)

--composeApplyEnvContIsCompose : ∀ {τs ϕ ϕ'} → (env : Env τs) → (cont1 : Cont τs ϕ) → (cont2 : Cont (single ϕ) ϕ') → applyVSCont (applyEnvCont env cont1) cont2 ≡ applyEnvCont env (composeCont cont1 cont2)
--composeApplyEnvContIsCompose env (cl ∷ cont1) cont2 = refl
--composeApplyEnvContIsCompose (v ∷ ε) ε cont2 = refl
