module _ where

module 1:Library where
  -- 1. Generic library definitions

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  add : ℕ → ℕ → ℕ
  add zero m = m
  add (succ n) m = succ (add n m)

  data Fin : ℕ → Set where
    zero : ∀ {n} → Fin (succ n)
    succ : ∀ {n} → Fin n → Fin (succ n)

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

  data Eq {A : Set} (a : A) : A → Set where
    refl : Eq a a

  _≡_ = Eq

  infixr 5 _∷_
  data List (X : Set) : Set where
    ε   : List X
    _∷_ : X → List X → List X

  data All {Ω : Set} (X : Ω → Set) : List Ω → Set where
    ε   : All X ε
    _∷_ : ∀ {ω ωs} → X ω → All X ωs → All X (ω ∷ ωs)

  data All₁ {Ω : Set} (X : Ω → Set₁) : List Ω → Set₁ where
    ε   : All₁ X ε
    _∷_ : ∀ {ω ωs} → X ω → All₁ X ωs → All₁ X (ω ∷ ωs)

  data Any {Ω : Set} (X : Ω → Set) : List Ω → Set where
    here  : ∀ {ω ωs} → X ω → Any X (ω ∷ ωs)
    there : ∀ {ω ωs} → Any X ωs → Any X (ω ∷ ωs)

  Has : {Ω : Set} → List Ω → Ω → Set
  Has ωs ω = Any (Eq ω) ωs

  data All× {Ω Ψ : Set} (X : Ω → Set) (Y : Ψ → Set) : Ω × Ψ → Set where
    _,_ : ∀ {ω ψ} → X ω → Y ψ → All× X Y (ω , ψ)

  data AllΣ {Ω : Set} {X : Ω → Set} (P : ∀ ω → X ω → Set) : Σ Ω X → Set where
    _,,_ : (ω : Ω) → {x : X ω} → P ω x → AllΣ P (ω ,, x)

  data AllAll {Ω : Set} {X : Ω → Set} (P : ∀ ω → X ω → Set) : ∀ ωs → All X ωs → Set where
    ε   : AllAll P ε ε
    _∷_ : ∀ {ω ωs x xs} → P ω x → AllAll P ωs xs → AllAll P (ω ∷ ωs) (x ∷ xs)

  data AllAny {Ω : Set} {X : Ω → Set} (P : ∀ ω → X ω → Set) : ∀ ωs → Any X ωs → Set where
    here  : ∀ {ω ωs x} → P ω x → AllAny P (ω ∷ ωs) (here x)
    there : ∀ {ω ωs xᵢ} → AllAny P ωs xᵢ → AllAny P (ω ∷ ωs) (there xᵢ)

  -- Functorial map for List
  mapList : {X Y : Set} → (X → Y) → (List X → List Y)
  mapList f  ε       = ε
  mapList f (x ∷ xs) = f x ∷ mapList f xs

  -- Functorial map for All
  mapAll : {Ω : Set} {X Y : Ω → Set} → (∀ {ω} → X ω → Y ω) → (∀ {ωs} → All X ωs → All Y ωs)
  mapAll f  ε       = ε
  mapAll f (x ∷ xs) = f x ∷ mapAll f xs

  -- Functorial map for Any
  mapAny : {Ω : Set} {X Y : Ω → Set} → (∀ {ω} → X ω → Y ω) → (∀ {ωs} → Any X ωs → Any Y ωs)
  mapAny f (here x)   = here (f x)
  mapAny f (there xᵢ) = there (mapAny f xᵢ)

  -- Functorial map for AllAll
  mapAllAll
      : {Ω : Set} {X Y : Ω → Set} {AllX : ∀ ω → X ω → Set} {AllY : ∀ ω → Y ω → Set}
      → (f : ∀ {ω} → X ω → Y ω)
      → (allF : ∀ {ω x} → AllX ω x → AllY ω (f x))
      → ∀ {ωs xs} → AllAll AllX ωs xs → AllAll AllY ωs (mapAll f xs)
  mapAllAll f allF  ε       = ε
  mapAllAll f allF (p ∷ ps) = allF p ∷ mapAllAll f allF ps

  -- Functorial map for AllAny
  mapAllAny
      : {Ω : Set} {X Y : Ω → Set} {AllX : ∀ ω → X ω → Set} {AllY : ∀ ω → Y ω → Set}
      → (f : ∀ {ω} → X ω → Y ω)
      → (allF : ∀ {ω x} → AllX ω x → AllY ω (f x))
      → ∀ {ωs xs} → AllAny AllX ωs xs → AllAny AllY ωs (mapAny f xs)
  mapAllAny f allF (here p)   = here (allF p)
  mapAllAny f allF (there pᵢ) = there (mapAllAny f allF pᵢ)

  identity : {X : Set} → X → X
  identity a = a

  cong : {X Y : Set} → (f : X → Y) → ∀ {x x'} → x ≡ x' → f x ≡ f x'
  cong f refl = refl

  transport : {Ω : Set} → (X : Ω → Set) → ∀ {ω ω'} → ω ≡ ω' → X ω → X ω'
  transport X refl x = x

  $0 : ∀ {Ω ω₀ ωs}             → Has {Ω} (ω₀ ∷ ωs) ω₀
  $1 : ∀ {Ω ω₀ ω₁ ωs}          → Has {Ω} (ω₀ ∷ ω₁ ∷ ωs) ω₁
  $2 : ∀ {Ω ω₀ ω₁ ω₂ ωs}       → Has {Ω} (ω₀ ∷ ω₁ ∷ ω₂ ∷ ωs) ω₂
  $3 : ∀ {Ω ω₀ ω₁ ω₂ ω₃ ωs}    → Has {Ω} (ω₀ ∷ ω₁ ∷ ω₂ ∷ ω₃ ∷ ωs) ω₃
  $4 : ∀ {Ω ω₀ ω₁ ω₂ ω₃ ω₄ ωs} → Has {Ω} (ω₀ ∷ ω₁ ∷ ω₂ ∷ ω₃ ∷ ω₄ ∷ ωs) ω₄
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2
  $4 = there $3

  get : {Ω : Set} {X : Ω → Set} → ∀ {ω ωs} → All X ωs → Has ωs ω → X ω
  get (x ∷ xs) (here refl) = x
  get (x ∷ xs) (there i)   = get xs i

  get2 : {Ω : Set} {X : Ω → Set} {P : ∀ ω → X ω → Set} → ∀ {ω ωs xs} → AllAll P ωs xs → (i : Has ωs ω) → P ω (get xs i)
  get2 (p ∷ ps) (here refl) = p
  get2 (p ∷ ps) (there i)   = get2 ps i

  infixr 5 _++_
  _++_ : {A : Set} → List A → List A → List A
  ε        ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  has-skip : {Ω : Set} → {τs : List Ω} → {τ : Ω} → (ρs : List Ω) → Has τs τ → Has (ρs ++ τs) τ
  has-skip  ε       i = i
  has-skip (ρ ∷ ρs) i = there (has-skip ρs i)

  has-append : {Ω : Set} → {τs : List Ω} → {τ : Ω} → (ρs : List Ω) → Has τs τ → Has (τs ++ ρs) τ
  has-append ρs (here e)  = here e
  has-append ρs (there i) = there (has-append ρs i)

  has-splice : {Ω : Set} → {τ : Ω} → (τs τs' ρs : List Ω) → Has (τs ++ τs') τ → Has (τs ++ ρs ++ τs') τ
  has-splice  ε       τs' ρs  i        = has-skip ρs i
  has-splice (τ ∷ τs) τs' ρs (here e)  = here e
  has-splice (τ ∷ τs) τs' ρs (there i) = there (has-splice τs τs' ρs i)

  has-abs : {Ω : Set} → {τ : Ω} → (ϕ : Ω) → (τs ρs : List Ω) → Has (ϕ ∷ τs) τ → Has (ϕ ∷ ρs ++ τs) τ
  has-abs ϕ τs ρs i = has-splice (ϕ ∷ ε) τs ρs i

  has-cons : {Ω : Set} → {τs : List Ω} → {τ ϕ : Ω} → Has τs τ → Has (τ ∷ τs) ϕ → Has τs ϕ
  has-cons i (here refl) = i
  has-cons i (there j)   = j

  has-prepend : {Ω : Set} → {τs τs' : List Ω} → (∀ {τ} → Has τs τ → Has τs' τ) → (σs : List Ω) → (∀ {τ} → Has (σs ++ τs) τ → Has (σs ++ τs') τ)
  has-prepend f  ε        x        = f x
  has-prepend f (c ∷ cs) (here x)  = here x
  has-prepend f (c ∷ cs) (there x) = there (has-prepend f cs x)

open 1:Library

module 2:Types where
  -- types

  infixr 5 _⇒_
  data Type : Set where
    _⇒_      : Type → Type → Type -- function
    #Sum     : List Type → Type   -- sum of a list of types
    #Product : List Type → Type   -- product of a list of types
    #Nat     : Type               -- natural number
    #Conat   : Type               -- conatural number (potentially infinite number)
    #Stream  : Type → Type        -- stream (infinite sequence)
    #Cnt     : Type → Type

  -- Empty sum
  #Void : Type
  #Void = #Sum ε
  
  -- Empty product
  #Unit : Type
  #Unit = #Product ε
  
  -- Sum of two types
  #Either : Type → Type → Type
  #Either σ τ = #Sum (σ ∷ τ ∷ ε)
  
  -- Product of two types
  #Pair : Type → Type → Type
  #Pair σ τ = #Product (σ ∷ τ ∷ ε)

  -- Bool
  #Bool : Type
  #Bool = #Either #Unit #Unit
  
  -- Maybe
  #Maybe : Type → Type
  #Maybe τ = #Either #Unit τ

open 2:Types

module 3:Rules where
  -- introduction and elimination rules

  data Intr (%Abstraction : Type → Type → Set) (%Value : Type → Set) : Type → Set where
    intrArrow   : ∀ {ρ τ}  → %Abstraction ρ τ                                → Intr %Abstraction %Value (ρ ⇒ τ)
    intrSum     : ∀ {τs}   → Any %Value τs                                   → Intr %Abstraction %Value (#Sum τs)
    intrProduct : ∀ {τs}   → All %Value τs                                   → Intr %Abstraction %Value (#Product τs)
    intrNat     :            %Value (#Maybe #Nat)                            → Intr %Abstraction %Value  #Nat
    intrConat   :            Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Maybe ρ))  → Intr %Abstraction %Value  #Conat
    intrStream  : ∀ {τ}    → Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Pair τ ρ)) → Intr %Abstraction %Value (#Stream τ)
  
  data Elim (%Value : Type → Set) : Type → Type → Set where
    elimArrow   : ∀ {ρ τ}  → %Value ρ                                        → Elim %Value (ρ ⇒ τ)       τ
    elimSum     : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs                    → Elim %Value (#Sum τs)     ϕ
    elimProduct : ∀ {τs τ} → Has τs τ                                        → Elim %Value (#Product τs) τ
    elimNat     : ∀ {ϕ}    → %Value (#Maybe ϕ ⇒ ϕ)                           → Elim %Value  #Nat         ϕ
    elimConat   :                                                              Elim %Value  #Conat      (#Maybe #Conat)
    elimStream  : ∀ {τ}                                                      → Elim %Value (#Stream τ)  (#Pair τ (#Stream τ))
  
  data Expr (%A : Type → Type → Set) (%V : Type → Set) (τ : Type) : Set where
    intr : Intr %A %V τ               → Expr %A %V τ
    elim : ∀ {ϕ} → %V ϕ → Elim %V ϕ τ → Expr %A %V τ

    -- fix : ∀ {τ} → %V (τ ⇒ τ) → Expr %A %V τ
    call-with-cc : %V (#Cnt τ ⇒ τ) → Expr %A %V τ
    call-cnt : ∀ {σ} → %V σ → %V (#Cnt σ) → Expr %A %V τ

open 3:Rules

module 4:Utensils where
  -- boilerplate utensils for introduction and elimination rules

  -- Functorial map for Intr
  mapIntr
      : ∀ {%A1 %A2 %V1 %V2}
      → (%mapA : ∀ {ρ τ} → %A1 ρ τ → %A2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ} → Intr %A1 %V1 τ → Intr %A2 %V2 τ)
  mapIntr %mapA %mapV (intrArrow abs)           = intrArrow (%mapA abs) 
  mapIntr %mapA %mapV (intrSum vᵢ)              = intrSum (mapAny %mapV vᵢ)
  mapIntr %mapA %mapV (intrProduct vs)          = intrProduct (mapAll %mapV vs)
  mapIntr %mapA %mapV (intrNat v)               = intrNat (%mapV v)
  mapIntr %mapA %mapV (intrConat (ρ ,, v , f))  = intrConat (ρ ,, %mapV v , %mapV f)
  mapIntr %mapA %mapV (intrStream (ρ ,, v , f)) = intrStream (ρ ,, %mapV v , %mapV f)
  
  -- Functorial map for Elim
  mapElim : ∀ {%V1 %V2} → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ ϕ} → Elim %V1 τ ϕ → Elim %V2 τ ϕ)
  mapElim %mapV (elimArrow v)   = elimArrow (%mapV v)
  mapElim %mapV (elimSum fs)    = elimSum (mapAll %mapV fs)
  mapElim %mapV (elimProduct i) = elimProduct i
  mapElim %mapV (elimNat f)     = elimNat (%mapV f)
  mapElim %mapV  elimConat      = elimConat
  mapElim %mapV  elimStream     = elimStream

  -- Functorial map for Expr
  mapExpr
      : ∀ {%A1 %A2 %V1 %V2}
      → (%mapA : ∀ {ρ τ} → %A1 ρ τ → %A2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ} → Expr %A1 %V1 τ → Expr %A2 %V2 τ)
  mapExpr %mapA %mapV (intr rule)       = intr (mapIntr %mapA %mapV rule)
  mapExpr %mapA %mapV (elim value rule) = elim (%mapV value) (mapElim %mapV rule)
  mapExpr _ = {!!}

open 4:Utensils

module 5:Term where
  -- regular term representation

  mutual
    -- regular de-bruijn term
    data Term (Γ : List Type) (τ : Type) : Set where
      var  : Has Γ τ → Term Γ τ
      wrap : Expr (AbsTerm Γ) (Term Γ) τ → Term Γ τ
  
    AbsTerm : List Type → (Type → Type → Set)
    AbsTerm Γ ρ τ = Term (ρ ∷ Γ) τ

  -- Maps a function to each variable in a term
  {-# TERMINATING #-} -- terminating because it preserves structure
  mapTerm : ∀ {Γ Δ} → (∀ {τ} → Has Γ τ → Has Δ τ) → (∀ {τ} → Term Γ τ → Term Δ τ)
  mapTerm f (var x)     = var (f x)
  mapTerm f (wrap expr) = wrap (mapExpr (mapTerm (has-prepend f _)) (mapTerm f) expr)

  -- Expands context with one ignored variable
  ↑_ : ∀ {Γ ρ τ} → Term Γ τ → Term (ρ ∷ Γ) τ
  ↑ term = mapTerm there term

open 5:Term

module 6:SomeTerms where
  -- examples of terms

  #lambda : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  #lambda f = wrap (intr (intrArrow f))

  #apply : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  #apply f v = wrap (elim f (elimArrow v))
                        
  #compose : ∀ {Γ ρ σ τ} → Term Γ (ρ ⇒ σ) → Term Γ (σ ⇒ τ) → Term Γ (ρ ⇒ τ)
  #compose f g = #lambda (#apply (↑ g) (#apply (↑ f) (var $0)))
  
  #inl : ∀ {Γ σ τ} → Term Γ σ → Term Γ (#Either σ τ)
  #inl v = wrap (intr (intrSum (here v)))
  
  #inr : ∀ {Γ σ τ} → Term Γ τ → Term Γ (#Either σ τ)
  #inr v = wrap (intr (intrSum (there (here v))))
  
  #either : ∀ {Γ σ τ ϕ} → Term Γ (σ ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Either σ τ) → Term Γ ϕ
  #either f₁ f₂ v = wrap (elim v (elimSum (f₁ ∷ f₂ ∷ ε)))
  
  #unit : ∀ {Γ} → Term Γ #Unit
  #unit = wrap (intr (intrProduct ε))
  
  #pair : ∀ {Γ σ τ} → Term Γ σ → Term Γ τ → Term Γ (#Pair σ τ)
  #pair v₁ v₂ = wrap (intr (intrProduct (v₁ ∷ v₂ ∷ ε)))

  #fst : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ σ
  #fst v = wrap (elim v (elimProduct $0))

  #snd : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ τ
  #snd v = wrap (elim v (elimProduct $1))

  #mapPair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Pair ρ σ ⇒ #Pair ρ τ)
  #mapPair f = #lambda (#pair (#fst (var $0)) (#apply (↑ f) (#snd (var $0))))

  #nothing : ∀ {Γ τ} → Term Γ (#Maybe τ)
  #nothing = #inl #unit

  #just : ∀ {Γ τ} → Term Γ τ → Term Γ (#Maybe τ)
  #just v = #inr v

  #maybe : ∀ {Γ τ ϕ} → Term Γ ϕ → Term Γ (τ ⇒ ϕ) → Term Γ (#Maybe τ) → Term Γ ϕ
  #maybe f₁ f₂ v = #either (#lambda (↑ f₁)) f₂ v

  #mapMaybe : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe σ ⇒ #Maybe τ)
  #mapMaybe f = #lambda (#maybe #nothing (#lambda (#just (#apply (↑ ↑ f) (var $0)))) (var $0))

  #elimNat : ∀ {Γ ϕ} → Term Γ (#Maybe ϕ ⇒ ϕ) → Term Γ (#Nat ⇒ ϕ)
  #elimNat f = #lambda (wrap (elim (var $0) (elimNat (↑ f))))

  #buildConat : ∀ {Γ ρ} → Term Γ (ρ ⇒ #Maybe ρ) → Term Γ (ρ ⇒ #Conat)
  #buildConat f = #lambda (wrap (intr (intrConat (_ ,, var $0 , ↑ f))))

  #buildStream : ∀ {Γ τ ρ} → Term Γ (ρ ⇒ #Pair τ ρ) → Term Γ (ρ ⇒ #Stream τ)
  #buildStream f = #lambda (wrap (intr (intrStream (_ ,, var $0 , ↑ f))))

open 6:SomeTerms

module 7:CompiledTerm where
  -- compiled term representation

  infixr 5 _▸_
  mutual
    data TermC (Γ : List Type) (τ : Type) : Set where
      return : Has Γ τ → TermC Γ τ
      _▸_    : ∀ {ρ} → Expr (AbsTermC Γ) (Has Γ) ρ → TermC (ρ ∷ Γ) τ → TermC Γ τ

    AbsTermC : List Type → (Type → Type → Set)
    AbsTermC Γ σ τ = TermC (σ ∷ Γ) τ

  -- Compile-time introduction rule
  IntrC : List Type → Type → Set
  IntrC Γ τ = Intr (AbsTermC Γ) (Has Γ) τ

  -- Compile-time elimination rule
  ElimC : List Type → Type → Type → Set
  ElimC Γ τ ϕ = Elim (Has Γ) τ ϕ

  -- Maps a function to each variable in a term
  {-# TERMINATING #-} -- terminating because it preserves structure
  mapTermC : ∀ {Γ Δ τ} → (∀ {ϕ} → Has Γ ϕ → Has Δ ϕ) → (TermC Γ τ → TermC Δ τ)
  mapTermC f (return x) = return (f x)
  mapTermC f (expr ▸ term) = mapExpr (mapTermC (has-prepend f _)) f expr ▸ mapTermC (has-prepend f _) term

  -- Term consisting of a single expression
  pure : ∀ {Γ τ} → Expr (AbsTermC Γ) (Has Γ) τ → TermC Γ τ
  pure expr = expr ▸ return $0

open 7:CompiledTerm

-- compilation
module 8:Compilation where
  infixr 5 _∷ₗ_
  data Linear {Ω : Set} (%V : Ω → Set) (%E : List Ω → Set) : List Ω → Set where
    εₗ   : ∀ {ρs} → %E ρs → Linear %V %E ρs
    _∷ₗ_ : ∀ {ρ ρs} → %V ρ → Linear %V %E (ρ ∷ ρs) → Linear %V %E ρs

  mapLinear
      : {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set}
      → (∀ {τs} → %E1 τs → %E2 τs) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 τs)
  mapLinear f (εₗ x)   = εₗ (f x)
  mapLinear f (v ∷ₗ l) = v ∷ₗ mapLinear f l

  mapLinear'
      : {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} {Γ : List Ω}
      → (∀ {τs} → %E1 τs → %E2 (τs ++ Γ)) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 (τs ++ Γ))
  mapLinear' f (εₗ x)   = εₗ (f x)
  mapLinear' f (v ∷ₗ l) = v ∷ₗ mapLinear' f l

  linizeAny
      : {Ω : Set} {%V : Ω → Set} {τs : List Ω}
      → (κ : Ω → Ω) → Any (\τ → %V (κ τ)) τs → Linear %V (\ρs → Any (\τ → Has ρs (κ τ)) τs) ε
  linizeAny κ (here v)   = v ∷ₗ εₗ (here $0)
  linizeAny κ (there vᵢ) = mapLinear there (linizeAny κ vᵢ)

  linizeAll
      : {Ω : Set} {%V : Ω → Set} {τs : List Ω}
      → (κ : Ω → Ω) → All (\τ → %V (κ τ)) τs → Linear %V (\ρs → All (\τ → Has ρs (κ τ)) τs) ε
  linizeAll κ  ε       = εₗ ε
  linizeAll κ (v ∷ vs) = v ∷ₗ mapLinear' (\vs' → has-skip _ $0 ∷ mapAll (has-append _) vs') (linizeAll κ vs)

  linizeIntr : ∀ {%A %V τ} → Intr %A %V τ → Linear %V (\ρs → Intr %A (Has ρs) τ) ε
  linizeIntr (intrArrow e)             = εₗ (intrArrow e)
  linizeIntr (intrSum vᵢ)              = mapLinear intrSum (linizeAny identity vᵢ)
  linizeIntr (intrProduct vs)          = mapLinear intrProduct (linizeAll identity vs)
  linizeIntr (intrNat v)               = v ∷ₗ εₗ (intrNat $0)
  linizeIntr (intrConat (ρ ,, v , f))  = v ∷ₗ f ∷ₗ εₗ (intrConat (ρ ,, $1 , $0))
  linizeIntr (intrStream (ρ ,, v , f)) = v ∷ₗ f ∷ₗ εₗ (intrStream (ρ ,, $1 , $0))

  linizeElim : ∀ {%V τ ϕ} → Elim %V τ ϕ → Linear %V (\ρs → Elim (Has ρs) τ ϕ) ε
  linizeElim (elimArrow v)   = v ∷ₗ εₗ (elimArrow $0)
  linizeElim (elimSum f)     = mapLinear elimSum (linizeAll (\τ → τ ⇒ _) f)
  linizeElim (elimProduct i) = εₗ (elimProduct i)
  linizeElim (elimNat v)     = v ∷ₗ εₗ (elimNat $0)
  linizeElim  elimConat      = εₗ elimConat
  linizeElim  elimStream     = εₗ elimStream

  linizeExpr : ∀ {%A %V τ} → Expr %A %V τ → Linear %V (\ρs → Expr %A (Has ρs) τ) ε
  linizeExpr (intr rule)       = mapLinear intr (linizeIntr rule)
  linizeExpr (elim value rule) = value ∷ₗ mapLinear' (\rule' → elim (has-skip _ $0) (mapElim (has-append _) rule')) (linizeElim rule)
  linizeExpr _ = {!!}

  combine2 : ∀ {Γ ρ τ} → TermC Γ ρ → TermC (ρ ∷ Γ) τ → TermC Γ τ
  combine2 (return x)     term2 = mapTermC (has-cons x) term2
  combine2 (expr ▸ term1) term2 = expr ▸ combine2 term1 (mapTermC (has-abs _ _ _) term2)

  combineL : ∀ {Γ Δ τ} → Linear (TermC Γ) (\ρs → Expr (AbsTermC Γ) (Has ρs) τ) Δ → TermC (Δ ++ Γ) τ
  combineL (εₗ expr)   = pure (mapExpr (mapTermC (has-abs _ _ _)) (has-append _) expr)
  combineL (term ∷ₗ l) = combine2 (mapTermC (has-skip _) term) (combineL l)

  seqize : ∀ {Γ τ} → Expr (AbsTermC Γ) (TermC Γ) τ → TermC Γ τ
  seqize expr = combineL (linizeExpr expr)

  -- Transforms regular representation of a term into compiled representation
  {-# TERMINATING #-} -- terminating because `mapExpr` preserves structure
  compile : ∀ {Γ τ} → Term Γ τ → TermC Γ τ
  compile (var x)     = return x
  compile (wrap expr) = seqize (mapExpr compile compile expr)

open 8:Compilation

-- run-time term representation
module 9:Runtime where
  mutual
    data Value (δ : Type) : Type → Set where
      construct : ∀ {τ} → Intr (Closure δ) (Value δ) τ → Value δ τ
      mkCnt : ∀ {τ} → CallStack τ δ → Value δ (#Cnt τ)

    data Closure (δ : Type) (ρ τ : Type) : Set where
      _&_ : ∀ {Γ} → Env δ Γ → TermC (ρ ∷ Γ) τ → Closure δ ρ τ

    -- A list of values for each type in Γ
    Env : (δ : Type) → List Type → Set
    Env δ Γ = All (Value δ) Γ

    -- A composable sequence of closures
    data CallStack : Type → Type → Set where
      ε   : ∀ {τ} → CallStack τ τ
      _∷_ : ∀ {ρ σ τ} → Closure τ ρ σ → CallStack σ τ → CallStack ρ τ

  {-
  -- Run-time introduction rule
  IntrR : Type → Set
  IntrR τ = Intr (Closure Value τ

  -- Run-time elimination rule
  ElimR : Type → Type → Set
  ElimR τ ϕ = Elim Value τ ϕ
  -}

  -- A term and an environment of values for each variable it references
  data Thunk (δ : Type) (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env δ Γ → TermC Γ τ → Thunk δ τ

  -- Computation state
  -- * a thunk that is currently being evaluated
  -- * and a continuation which will be applied when we finish evaluating the thunk
  data Machine : Type → Set where
    _▹_ : ∀ {σ τ} → Thunk τ σ → CallStack σ τ → Machine τ

  -- Result of a single computation step
  -- * final value if the computation finishes
  -- * next computation state if it doesn't
  data Step (τ : Type) : Set where
    finish   : Value τ τ → Step τ
    continue : Machine τ → Step τ

  -- Plugs a value into a closure, producing a thunk
  composeValueClosure : ∀ {δ σ τ} → Value δ σ → Closure δ σ τ → Thunk δ τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  {-
  -- Composes two callstacks
  composeStackStack : ∀ {l1 l2 ρ σ τ} → CallStack l1 ρ σ → CallStack l2 σ τ → CallStack (l1 ++ l2) ρ τ
  composeStackStack  ε                 stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  -- Appends a callstack to the current callstack of a machine
  composeMachineStack : ∀ {l σ τ} → Machine σ → CallStack l σ τ → Machine τ
  composeMachineStack (thunk ▹ stack1) stack2 = thunk ▹ composeStackStack stack1 stack2
  -}

  -- Applies a value to a callstack
  composeValueStack : ∀ {σ τ} → Value τ σ → CallStack σ τ → Step τ
  composeValueStack value  ε                = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ▹ stack)
  --composeValueStack value (mkLabel stack) = {!!}

  {-
  -- Composes a computation step and a callstack
  -- * for a finished computation: applies the callstack to the result
  -- * for a non-finished computation: append the callstack the current callstack of the machine
  composeStepStack : ∀ {n σ τ} → Step σ → CallStack n σ τ → Step τ
  composeStepStack (finish value)     stack = composeValueStack value stack
  composeStepStack (continue machine) stack = continue (composeMachineStack machine stack)
  -}

  -- Transforms compiled representation of a closed term into run-time representation
  -- * initial environment is empty
  -- * initial continuation is empty as well
  load : ∀ {τ} → TermC ε τ → Machine τ
  load term = (ε & term) ▹ ε

open 9:Runtime

-- operational semantics for elimination rules
module 10:OperationalElimination where
  eliminateArrow : ∀ {lbls ρ τ ϕ} → Elim (Value lbls) (ρ ⇒ τ) ϕ → (Value lbls) (ρ ⇒ τ) → Thunk lbls ϕ
  eliminateArrow (elimArrow value) (construct (intrArrow closure)) = composeValueClosure value closure
  --eliminateArrow (elimArrow value) (mkGoto i) = {!!}

  eliminateSum : ∀ {lbls τs ϕ} → Elim (Value lbls) (#Sum τs) ϕ → Value lbls (#Sum τs) → Thunk lbls ϕ
  eliminateSum (elimSum (f ∷ fs)) (construct (intrSum (here v))) = (f ∷ v ∷ ε) & compile (#apply (var $0) (var $1))
  eliminateSum (elimSum (f ∷ fs)) (construct (intrSum (there vᵢ))) = eliminateSum (elimSum fs) (construct (intrSum vᵢ))

  eliminateProduct : ∀ {lbls τs ϕ} → Elim (Value lbls) (#Product τs) ϕ → Value lbls (#Product τs) → Thunk lbls ϕ
  eliminateProduct (elimProduct i) (construct (intrProduct vs)) = (get vs i ∷ ε) & compile (var $0)

  eliminateNat' : ∀ {lbls ϕ} → Elim (Value lbls) #Nat ϕ → Value lbls #Nat → Thunk lbls ϕ
  eliminateNat' (elimNat f) (construct (intrNat v)) =
      (f ∷ v ∷ ε) &
      ( intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
      ▸ intr (intrArrow (elim $0 (elimNat $2) ▸ pure (intr (intrSum (there (here $0))))))
      ▸ elim $3 (elimSum ($1 ∷ $0 ∷ ε))
      ▸ pure (elim $3 (elimArrow $0))
      )

{-
  eliminateConat' : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat' elimConat (construct (intrConat (ρ ,, v , f))) =
      (f ∷ v ∷ ε) &
      ( elim $0 (elimArrow $1)
      ▸ intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
      ▸ intr (intrArrow (intr (intrConat (ρ ,, $0 , $3)) ▸ pure (intr (intrSum (there (here $0))))))
      ▸ pure (elim $2 (elimSum ($1 ∷ $0 ∷ ε)))
      )

  eliminateStream' : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream' elimStream (construct (intrStream (ρ ,, v , f))) =
      (f ∷ v ∷ ε) &
      ( elim $0 (elimArrow $1)
      ▸ elim $0 (elimProduct $0)
      ▸ elim $1 (elimProduct $1)
      ▸ intr (intrStream (ρ ,, $0 , $3))
      ▸ pure (intr (intrProduct ($2 ∷ $0 ∷ ε)))
      )
      -}

  eliminate : ∀ {τ ϕ lbls} → Elim (Value lbls) τ ϕ → Value lbls τ → Thunk lbls ϕ
  eliminate {ρ ⇒ τ}       = eliminateArrow
  eliminate {#Sum τs}     = eliminateSum
  eliminate {#Product τs} = eliminateProduct
  eliminate {#Nat}        = eliminateNat'
  eliminate {_} = {!!}
  -- eliminate {#Conat}      = eliminateConat'
  -- eliminate {#Stream τ}   = eliminateStream'

open 10:OperationalElimination

-- operational semantics
module 11:Operational where
  -- Given an environment, transforms compile-time introduction rule into a run-time introduction rule
  plugEnvIntr : ∀ {lbls Γ τ} → Env lbls Γ → Intr (AbsTermC Γ) (Has Γ) τ → Intr (Closure lbls) (Value lbls) τ
  plugEnvIntr env rule = mapIntr (\term → env & term) (\x → get env x) rule

  -- Given an environment, transforms compile-time elimination rule into a run-time elimination rule
  plugEnvElim : ∀ {lbls Γ τ ϕ} → Env lbls Γ → Elim (Has Γ) τ ϕ → Elim (Value lbls) τ ϕ
  plugEnvElim env rule = mapElim (\x → get env x) rule

  -- Performs a single computation step
  reduce : ∀ {τ} → Machine τ → Step τ
  reduce ((env & return x) ▹ stack) = composeValueStack (get env x) stack
  reduce ((env & (intr rule ▸ term')) ▹ stack) = continue (((value ∷ env) & term') ▹ stack)
    where
      value : Value _ _
      value = construct (plugEnvIntr env rule)
  reduce ((env & (elim x rule ▸ term')) ▹ stack) = continue (thunk ▹ ((env & term') ∷ stack))
    where
      thunk : Thunk _ _
      thunk = eliminate (plugEnvElim env rule) (get env x)
  --reduce ((env & (fix f ▸ term')) ▹ stack) = continue (((fix f ∷ env) & term') ▹ stack)
  reduce ((env & (call-with-cc f ▸ term')) ▹ stack) with get env f
  ... | construct (intrArrow closure) = continue (composeValueClosure (mkCnt cont) closure ▹ cont)
    where
      cont : CallStack _ _
      cont = (env & term') ∷ stack
  reduce ((env & (call-cnt x c ▸ term')) ▹ stack) with get env c
  ... | mkCnt stack' = composeValueStack (get env x) stack'

open 11:Operational

-- example
module _ where
  #absurd : ∀ {Γ} τ → Term Γ #Void → Term Γ τ
  #absurd τ v = wrap (elim v (elimSum ε))

  ex : ∀ τ → Term ε (((τ ⇒ #Void) ⇒ #Void) ⇒ τ)
  ex τ = #lambda (wrap (call-with-cc (#lambda (#absurd τ (wrap (elim (var $1) (elimArrow (#lambda (wrap (call-cnt (var $0) (var $1)))))))))))

  ex2 : ∀ τ ρ → Term ε (((τ ⇒ ρ) ⇒ τ) ⇒ τ)
  ex2 τ ρ = #lambda (wrap (call-with-cc (#lambda (wrap (elim (var $1) (elimArrow (#lambda (wrap (call-cnt (var $0) (var $1))))))))))
