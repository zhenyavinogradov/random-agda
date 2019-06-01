-- untyped lambda calculus
module _ where

module _ where
  -- function
  module _ where
    _▹_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
    (f ▹ g) x = g (f x)

    _#_ : {A B : Set} → A → (A → B) → B
    x # f = f x

  -- dependendent pair
  module _ where
    record Σ (A : Set) (B : A → Set) : Set where
      field
        π₁ : A
        π₂ : B π₁

    ∃ : {A : Set} → (B : A → Set) → Set
    ∃ {A} B = Σ A B

  -- finite product
  module _ where
    record _×_ (A B : Set) : Set where
      field
        fst : A
        snd : B

  -- bool
  module _ where
    data Bool : Set where
      false true : Bool

  -- natural
  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

    _=?_ : ℕ → ℕ → Bool
    zero =? zero = true
    zero =? succ j = false
    succ i =? zero = false
    succ i =? succ j = i =? j

infix 5 ƛ_
infixr 10 _^_
data Lam : Set where
  $   : ℕ → Lam
  _^_ : Lam → Lam → Lam
  ƛ_  : Lam → Lam

-- conversion
module _ where
  subst : Lam → ℕ → Lam → Lam
  subst ($ j) i g = (i =? j) # \{ false → $ j ; true → g }
  subst (f₁ ^ f₂) i g = subst f₁ i g ^ subst f₂ i g
  subst (ƛ f) i g = ƛ subst f (succ i) g
  
  infix 4 _⇒^_
  data _⇒^_ : Lam → Lam → Set where
    β-step : ∀ {f g} → (ƛ f) ^ g ⇒^ subst f zero g

  infix 4 _⇒_
  data _⇒_ : Lam → Lam → Set where
    here : ∀ {f f'} → f ⇒^ f' → f ⇒ f'
    appL : ∀ {f f' g} → f ⇒ f' → f ^ g ⇒ f' ^ g
    appR : ∀ {f g g'} → g ⇒ g' → f ^ g ⇒ f ^ g'
    abs  : ∀ {f f'} → f ⇒ f' → ƛ f ⇒ ƛ f'

  infix 4 _⇒*_
  data _⇒*_ : Lam → Lam → Set where
    pure  : ∀ {f f'} → f ⇒ f' → f ⇒* f'
    refl  : ∀ {f} → f ⇒* f
    trans : ∀ {f g h} → f ⇒ g → g ⇒* h → f ⇒* h

  infix 4 _=β_
  _=β_ : Lam → Lam → Set
  _=β_ = {!!}

  record normal-form (f : Lam) : Set where
    field
      nf : Lam
      reduction : f ⇒* nf
      normal : {h : Lam} → f ⇒* h → h ⇒* nf


  church-rosser : ∀ {f g₁ g₂} → f ⇒* g₁ → f ⇒* g₂ → ∃ \(h : Lam) → (g₁ ⇒* h) × (g₂ ⇒* h)
  church-rosser = {!!}

module _ where
  $0 : Lam
  $0 = $ 0

  $1 : Lam
  $1 = $ 1

-- terms
module _ where
  -- infinite reduction chain
  module _ where
    eΩ : Lam
    eΩ = eω ^ eω where eω = ƛ $0 ^ $0

    _ : eΩ ⇒ eΩ
    _ = here β-step

  -- general recursion
  module _ where
    eY : Lam
    eY = ƛ (eY' ^ eY') where eY' = ƛ $1 ^ ($0 ^ $0)

    _ : {f : Lam} → eY ^ f =β f ^ (eY ^ f)
    _ = {!!}

 
  -- naturals
  module _ where
   -- zero : 1 ⇛ ℕ
   eZero : Lam
   eZero = ƛ ƛ $1

   -- succ : ℕ ⇛ ℕ
   eSucc : Lam → Lam
   eSucc k = ƛ ƛ ($0 ^ k)
   
   {-
   case : A, (A ⇛ A) → ℕ ⇛ A
   case (f, g) zero = f
   case (f, g) (succ k) = g (case (f,  g) k)
   -}
