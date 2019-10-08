module _ where

-- lib
module _ where
  _€_ : {A B : Set} → A → (A → B) → B
  x € f = f x

  record ⊤ : Set where
    constructor tt

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  single : {A : Set} → A → List A
  single a = a ∷ ε

  mapList : {A B : Set} → (A → B) → (List A → List B)
  mapList f ε = ε
  mapList f (a ∷ as) = f a ∷ mapList f as

  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  data Elem {A : Set} : List A → Set where
    here : ∀ {a as} → Elem (a ∷ as)
    there : ∀ {a as} → Elem as → Elem (a ∷ as)

  elemr : {A : Set} {ys : List A} → (xs : List A) → Elem ys → Elem (xs ++ ys)
  elemr ε i = i
  elemr (x ∷ xs) i = there (elemr xs i)

  elemins : {A : Set} {a : A} {ys : List A} → (xs : List A) → Elem (xs ++ ys) → Elem (xs ++ (a ∷ ys))
  elemins ε i = there i
  elemins (x ∷ xs) here = here
  elemins (x ∷ xs) (there i) = there (elemins xs i)

  elemmap : {A B : Set} → {xs : List A} → (f : A → B) → Elem xs → Elem (mapList f xs)
  elemmap f here = here
  elemmap f (there i) = there (elemmap f i)

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  mapAll : {A : Set} {P Q : A → Set} → ({a : A} → P a → Q a) → {as : List A} → All P as → All Q as
  mapAll f ε = ε
  mapAll f (Pa ∷ Pas) = f Pa ∷ mapAll f Pas

  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (succ n)
    succ : {n : ℕ} → Fin n → Fin (succ n)

  data Vector (A : Set) : ℕ → Set where
    ε : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  data AllV {A : Set} (P : A → Set) : {n : ℕ} → Vector A n → Set where
    ε : AllV P ε
    _∷_ : {n : ℕ} {a : A} {as : Vector A n} → P a → AllV P as → AllV P (a ∷ as)

  postulate String : Set
  {-# BUILTIN STRING String #-}

  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a
  {-# BUILTIN EQUALITY _≡_ #-}

  transport : {A : Set} → (P : A → Set) → {a a' : A} → a ≡ a' → P a → P a'
  transport P refl Pa = Pa

  cong : {A B : Set} → (f : A → B) → {a a' : A} → a ≡ a' → f a ≡ f a'
  cong f refl = refl


-- Valid
module _ where
  data Type : Set where
    -- π σ : List Type → Type
    _⇒_ : Type → Type → Type
    Nat : Type

  Context : Set
  Context = List Type
  
  data Term (Γ : Context) : Set where
    var : (i : Elem Γ) → Term Γ
    --llet : (ρ τ : Type) → (x : Var) → Term{-ρ-} → Term{-x:ρ⊢τ-} → Term{-τ-}
  
  {-
    π-intr : (n : ℕ) → (τs : Vector Type n) → (Ms : Vector Term{-τᵢ-} n) → Term{-π τs-}
    π-elim : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-π τs-} → Term{-τᵢ-}
  
    σ-intr : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-τᵢ-} → Term{-σ τs-}
    σ-elim : (n : ℕ) → (τs : Vector Type n) → (ρ : Type) → (Ms : Vector (Abs Term{-τᵢ⊢ρ-}) n) → Term{-σ τs-} → Term{-ρ-}
    -}
  
    ⇒-intr : (ρ τ : Type) → Term (ρ ∷ Γ) {-τ-} → Term Γ {-ρ⇒τ-}
    ⇒-elim : (ρ τ : Type) → Term Γ {-ρ-} → Term Γ {-ρ⇒τ-} → Term Γ {-τ-}
  
    N-elim : (ρ : Type) → Term Γ {-ρ-} → Term (ρ ∷ Γ) {-ρ-} → Term Γ {-ℕ-} → Term Γ {-ρ-}
    N-zero : Term Γ {-ℕ-}
    N-succ : Term Γ {-ℕ-} → Term Γ {-ℕ-}
  
  {-
    M-nothing : (τ : Type) → Term{-Maybe τ-}
    M-just : (τ : Type) → Term{-τ-} → Term{-Maybe τ-}
    M-elim : (τ ρ : Type) → Term{-ρ-} → {-(x : Var) →-} Term{-x:τ⊢ρ-} → Term{-Maybe τ-} → Term{-ρ-}
  
    S-intr : (τ ρ : Type) → {-(x : Var) →-} Term{-x:ρ⊢τ-} → Term{-x:ρ⊢ρ-} → Term{-ρ-} → Term{-Stream τ-}
    S-head : (τ : Type) → Term{-Stream τ-} → Term{-τ-}
    S-tail : (τ : Type) → Term{-Stream τ-} → Term{-Stream τ-}
  
    CoN-intr : (ρ : Type) → {-(x : Var) →-} Term{-x:ρ⊢ρ-} → Term{-ρ-} → Term{-CoN-}
    CoN-elim : Term{-CoN-} → Term{-Maybe CoN-}
    -}
  
  data Has : (Γ : Context) → Elem Γ → Type → Set where
    here : ∀ {Γ τ} → Has (τ ∷ Γ) here τ
    there : ∀ {Γ i τ p} → Has Γ i τ → Has (p ∷ Γ) (there i) τ
  
  data Valid : (Γ : Context) → Type → Term Γ → Set where
    #var : ∀ {Γ} → (i : Elem Γ) → (τ : Type) → (h : Has Γ i τ) → Valid Γ τ (var i)
    -- #llet : ∀ {Γ} → (ρ τ : Type) → (x : Var) → (N : Term{-ρ-}) → Valid Γ ρ N → (M : Term{-x:ρ⊢τ-}) → Valid ((x , ρ) ∷ Γ) τ M → Valid Γ τ (llet ρ τ x N M)
  
  {-
    #π-intr : ∀ {Γ} → (n : ℕ) → (τs : Vector Type n) → (Ms : Vector Term{-τᵢ-} n) → AllV (Valid Γ {!!}
    #π-elim : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-π τs-} → Term{-τᵢ-} → {!!}
  
    #σ-intr : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-τᵢ-} → Term{-σ τs-} → {!!}
    #σ-elim : (n : ℕ) → (τs : Vector Type n) → (ρ : Type) → (Ms : Vector (Abs Term{-τᵢ⊢ρ-}) n) → Term{-σ τs-} → Term{-ρ-} → {!!}
    -}
  
    #⇒-intr : ∀ {Γ} → (ρ τ : Type) → (M : Term (ρ ∷ Γ) {-τ-}) → Valid (ρ ∷ Γ) τ M → Valid Γ (ρ ⇒ τ) (⇒-intr ρ τ M)
    #⇒-elim : ∀ {Γ} → (ρ τ : Type)
            → (N : Term Γ {-ρ-}) → (#N : Valid Γ ρ N)
            → (M : Term Γ {-ρ⇒τ-}) → (#M : Valid Γ (ρ ⇒ τ) M)
            → Valid Γ τ (⇒-elim ρ τ N M)
  
    #N-zero : ∀ {Γ} → Valid Γ Nat N-zero
    #N-succ : ∀ {Γ} → (M : Term Γ {-ℕ-}) → Valid Γ Nat M → Valid Γ Nat (N-succ M)
    #N-elim : ∀ {Γ} → (ρ : Type)
           → (N₀ : Term Γ {-ρ-}) → Valid Γ ρ N₀
           → (Nₛ : Term (ρ ∷ Γ) {-ρ-}) → Valid (ρ ∷ Γ) ρ Nₛ
           → (M : Term Γ {-ℕ-}) → Valid Γ Nat M
           → Valid Γ ρ (N-elim ρ N₀ Nₛ M)


{-
TypeVal : Type → Set
TypeVal (ρ ⇒ τ) = TypeVal ρ → TypeVal τ
TypeVal Nat = ℕ

ContextVal : Context → Set
ContextVal ε = ⊤
ContextVal ((_ , τ) ∷ Γ) = TypeVal τ × ContextVal Γ

ℕcase : {X : Set} → (n : ℕ) → X → (X → X) → X
ℕcase zero f₀ fₛ = f₀
ℕcase (succ n) f₀ fₛ = fₛ (ℕcase n f₀ fₛ)

TermVal : {Γ : Context} → {τ : Type} → (M : Term) → Valid Γ τ M → ContextVal Γ → TypeVal τ
TermVal _ (#var x τ h) vΓ = {!!}
-- TermVal _ (#llet ρ τ x N #N M #M) vΓ = TermVal M #M (TermVal N #N vΓ , vΓ)
TermVal _ (#⇒-intr ρ τ x M #M) vΓ = \vx → TermVal M #M (vx , vΓ)
TermVal _ (#⇒-elim ρ τ N #N M #M) vΓ =  (TermVal M #M vΓ) (TermVal N #N vΓ)
TermVal _ #N-zero vΓ = zero
TermVal _ (#N-succ M #M) vΓ = succ (TermVal M #M vΓ)
TermVal _ (#N-elim τ N₀ #N₀ x Nₛ #Nₛ M #M) vΓ = ℕcase (TermVal M #M vΓ) (TermVal N₀ #N₀ vΓ) (\vx → TermVal Nₛ #Nₛ (vx , vΓ) )
-}


-- subst
module _ where
  fsucc : ∀ {Γ Δ} → (ρ : Type) → (Elem Γ → Elem Δ) → (Elem (ρ ∷ Γ) → Elem (ρ ∷ Δ))
  fsucc ρ f here = here
  fsucc ρ f (there i) = there (f i)
  
  mapTerm : ∀ {Γ Δ} → (Elem Γ → Elem Δ) → (Term Γ → Term Δ)
  mapTerm f (var i) = var (f i)
  mapTerm f (⇒-intr ρ τ M) = ⇒-intr ρ τ (mapTerm (fsucc ρ f) M) 
  mapTerm f (⇒-elim ρ τ N M) = ⇒-elim ρ τ (mapTerm f N) (mapTerm f M)
  mapTerm f (N-elim ρ N₀ Nₛ M) = N-elim ρ (mapTerm f N₀) (mapTerm (fsucc ρ f) Nₛ) (mapTerm f M)
  mapTerm f N-zero = N-zero
  mapTerm f (N-succ M) = N-succ (mapTerm f M)

  tsucc : ∀ {Γ} → (ρ : Type) → Term Γ → Term (ρ ∷ Γ)
  tsucc ρ M = mapTerm there M
  
{-
  skip' : ∀ {Γ Δ} Ω → (ρ : Type) → Subst Γ (Ω ++ Δ) → Subst (ρ ∷ Γ) (Ω ++ (ρ ∷ Δ))
  skip' Ω ρ γ = (var (elemr Ω here)) ∷ mapAll (mapvar (elemins Ω)) γ 

  ssucc : ∀ {Γ Δ} → (ρ : Type) → Subst Γ Δ → Subst Γ (ρ ∷ Δ)
  ssucc ρ γ = mapAll (tsucc ρ) γ
  
  skip : ∀ {Γ Δ} → (ρ : Type) → Subst Γ Δ → Subst (ρ ∷ Γ) (ρ ∷ Δ)
  skip ρ γ = var here ∷ ssucc ρ γ

  identity : (Γ : Context) → Subst Γ Γ
  identity ε = ε
  identity (ρ ∷ Γ) = skip ρ (identity Γ)

  identity' : (Ω Γ : Context) → Subst Γ (Ω ++ Γ)
  identity' Ω ε = ε
  identity' Ω (ρ ∷ Γ) = var (elemr Ω here) ∷ {!identity' (Ω ++ single ρ) Γ!}

  set : ∀ {Γ Δ} → (ρ : Type) → Term Δ {-ρ-} → Subst Γ Δ → Subst (ρ ∷ Γ) Δ
  set ρ U γ = U ∷ γ

  ↑ : (Γ : Context) → (ρ : Type) → Subst Γ (ρ ∷ Γ)
  ↑ Γ ρ = identity' (single ρ) Γ
  
  bind : ∀ {Γ Δ} → Subst Γ Δ → Term Γ → Term Δ
  bind γ (var j) = subvar γ j
  bind γ (⇒-intr ρ τ M) = ⇒-intr ρ τ (bind (skip ρ γ) M)
  bind γ (⇒-elim ρ τ N M) = ⇒-elim ρ τ (bind γ N) (bind γ M)
  bind γ (N-elim ρ N₀ Nₛ M) = N-elim ρ (bind γ N₀) (bind (skip ρ γ) Nₛ) (bind γ M) 
  bind γ N-zero = N-zero
  bind γ (N-succ M) = N-succ (bind γ M)
  
  subst : ∀ {Γ} → (ρ : Type) → Term Γ → Term (ρ ∷ Γ) → Term Γ
  subst {Γ} ρ N M = bind (N ∷ identity Γ) M

  compose' : ∀ {Γ Δ Ω} → Subst Δ Ω → Subst Γ Δ → Subst Γ Ω
  compose' γ₁ γ₂ = mapAll (bind γ₁) γ₂

  lem-bind-identity : (Γ : Context) → (M : Term Γ) → bind (identity Γ) M ≡ M
  lem-bind-identity = {!!}
  -}

  Subst% : (Γ Δ : Context) → Set
  Subst% Γ Δ = Elem Γ → Term Δ

  identity% : (Γ : Context) → Subst% Γ Γ
  identity% Γ = \i → var i

  set% : ∀ {Γ Δ} → (ρ : Type) → Term Δ → Subst% Γ Δ → Subst% (ρ ∷ Γ) Δ
  set% ρ U γ here = U
  set% ρ U γ (there i) = γ i

  up'% : ∀ {Γ} → (ρ : Type) → Subst% Γ (ρ ∷ Γ)
  up'% ρ = \i → var (there i)

  up% : ∀ {Γ Δ} → (ρ : Type) → Subst% Γ Δ → Subst% Γ (ρ ∷ Δ)
  up% ρ γ = \i → mapTerm there (γ i)

  {-
  fish% : ∀ {Γ Δ Ω} → Subst% Δ Ω → Subst% Γ Δ → Subst% Γ Ω
  fish% γ₁ γ₂ = \i → bind γ₁ (γ₂ i)
  -}

  _~%_ : {Γ Δ : Context} → (γ₁ γ₂ : Subst% Γ Δ) → Set
  γ₁ ~% γ₂ = ∀ i → γ₁ i ≡ γ₂ i

  Subst : Context → Context → Set
  Subst Γ Δ = All (\ρ → Term Δ) Γ

  subvar : ∀ {Γ Δ} → Subst Γ Δ → Elem Γ → Term Δ
  subvar (U ∷ γ) here = U
  subvar (U ∷ γ) (there i) = subvar γ i

  identity : (Γ : Context) → Subst Γ Γ
  identity Γ = {!!}

  set : ∀ {Γ Δ} → (ρ : Type) → Term Δ → Subst Γ Δ → Subst (ρ ∷ Γ) Δ
  set ρ U γ = {!!}

  up' : ∀ {Γ} → (ρ : Type) → Subst Γ (ρ ∷ Γ)
  up' ρ = {!!}

  up : ∀ {Γ Δ} → (ρ : Type) → Subst Γ Δ → Subst Γ (ρ ∷ Δ)
  up ρ γ = mapAll (tsucc ρ) γ

  _~_ : {Γ Δ : Context} → (γ₁ γ₂ : Subst Γ Δ) → Set
  γ₁ ~ γ₂ = {!!}

  skip : ∀ {Γ Δ} → (ρ : Type) → Subst Γ Δ → Subst (ρ ∷ Γ) (ρ ∷ Δ)
  skip ρ γ = set ρ (var here) (up ρ γ)
  
  bind : {Γ Δ : Context} → Subst Γ Δ → Term Γ → Term Δ
  bind γ (var i) = subvar γ i
  bind γ (⇒-intr ρ τ M) = ⇒-intr ρ τ (bind (skip ρ γ) M)
  bind γ (⇒-elim ρ τ N M) = ⇒-elim ρ τ (bind γ N) (bind γ M)
  bind γ (N-elim ρ N₀ Nₛ M) = N-elim ρ (bind γ N₀) (bind (skip ρ γ) Nₛ) (bind γ M)
  bind γ N-zero = N-zero
  bind γ (N-succ M) = N-succ (bind γ M)

  fish : ∀ {Γ Δ Ω} → Subst Δ Ω → Subst Γ Δ → Subst Γ Ω
  fish γ₁ γ₂ = {!!}

  subst : ∀ {Γ} → (ρ : Type) → Term Γ → Term (ρ ∷ Γ) → Term Γ
  subst {Γ} ρ N M = bind (set ρ N (identity Γ)) M


-- Red
module _ where
  data Red {Γ : Context} : Term Γ → Term Γ → Set where
    ⇒-elim-red : ∀ {ρ τ} N M → Red (⇒-elim ρ τ N (⇒-intr ρ τ M)) (subst ρ N M)
    N-elim-zero-red : ∀ {ρ} N₀ Nₛ → Red (N-elim ρ N₀ Nₛ N-zero) N₀
    N-elim-succ-red : ∀ {ρ} N₀ Nₛ M → Red (N-elim ρ N₀ Nₛ (N-succ M)) (subst ρ (N-elim ρ N₀ Nₛ M) Nₛ)
  
    ⇒-intr-red : ∀ {ρ τ M M'} → Red M M' → Red (⇒-intr ρ τ M) (⇒-intr ρ τ M')
    ⇒-elim-N-red : ∀ {ρ τ N N'} → (M : Term Γ) → Red N N' → Red (⇒-elim ρ τ N M) (⇒-elim ρ τ N' M)
    ⇒-elim-M-red : ∀ {ρ τ M M'} → (N : Term Γ) → Red M M' → Red (⇒-elim ρ τ N M) (⇒-elim ρ τ N M')
    N-succ-red : ∀ {M M'} → Red M M' → Red (N-succ M) (N-succ M')

  ⇒-elim-red' : ∀ {Γ Δ} → (γ : Subst Γ Δ) → ∀ {ρ τ} N M → Red (bind γ (⇒-elim ρ τ N (⇒-intr ρ τ M))) (bind (set ρ (bind γ N) γ) M)
  ⇒-elim-red' γ {ρ = ρ} N M = {!⇒-elim-red (bind γ N) (bind (skip ρ γ) M)!}
  
  lem-subst-red : ∀ {Γ Δ} → (γ : Subst Γ Δ) → {M M' : Term Γ} → Red M M' → Red (bind γ M) (bind γ M')
  lem-subst-red γ r = {!⇒-elim-red' γ N M!}


-- SN
module _ where
  data SN {Γ : Context} (M : Term Γ) : Set where
    mkSN : ((M' : Term Γ) → Red M M' → SN M') → SN M
  
  sn-zero : ∀ {Γ} → SN {Γ} N-zero
  sn-zero = mkSN \M' ()
  
  sn-succ : ∀ {Γ} → (M : Term Γ) → SN M → SN (N-succ M)
  sn-succ M (mkSN sM) = mkSN (\succM' → \{ (N-succ-red {M' = M'} r) → sn-succ M' (sM M' r)})


-- Val
module _ where
  TypeVal' : (Γ : Context) → (τ : Type) → (M : Term Γ) → Set
  TypeVal' Γ (ρ ⇒ τ) M = (U : Term Γ) → TypeVal' Γ ρ U → TypeVal' Γ τ (⇒-elim ρ τ U M)
  TypeVal' Γ Nat M = SN M

  prepend : ∀ {Γ} Ω → Term Γ → Term (Ω ++ Γ)
  prepend = {!!}

  TypeVal'' : (Γ : Context) → (τ : Type) → (M : Term Γ) → Set
  TypeVal'' Γ (ρ ⇒ τ) M = (Ω : Context) → (U : Term (Ω ++ Γ)) → TypeVal'' (Ω ++ Γ) ρ U → TypeVal'' (Ω ++ Γ) τ (⇒-elim ρ τ U (prepend Ω M))
  TypeVal'' Γ Nat M = SN M

{-
  tvmapsucc : {Γ : Context} → (ρ : Type) → (τ : Type) → (M : Term Γ) → TypeVal' Γ τ M → TypeVal' (ρ ∷ Γ) τ (mapvar (fsucc ρ) M)
  tvmapsucc ρ (σ ⇒ τ) M vM = {!!}
  tvmapsucc ρ Nat M vM = {!!}
  -}
  
  cr2 : ∀ {Γ} → (τ : Type) → (M M' : Term Γ) → Red M M' → TypeVal' Γ τ M → TypeVal' Γ τ M'
  cr2 (ρ ⇒ τ) M M' r vM = \N vN → cr2 τ (⇒-elim ρ τ N M) (⇒-elim ρ τ N M') (⇒-elim-M-red N r) (vM N vN)
  cr2 Nat M M' r (mkSN sM) = sM M' r
  
  cr2' : ∀ {Γ} → (τ : Type) → (M M' : Term Γ) → Red M M' → TypeVal'' Γ τ M → TypeVal'' Γ τ M'
  cr2' (ρ ⇒ τ) M M' r vM = \Ω N vN → cr2' τ (⇒-elim ρ τ N (prepend Ω M)) (⇒-elim ρ τ N (prepend Ω M')) (⇒-elim-M-red N {!lem-subst-red γ r!}) (vM Ω N vN)
  cr2' Nat M M' r (mkSN sM) = sM M' r
  
  data Neutral {Γ} : Term Γ → Set where
    n-var : ∀ {i} → Neutral (var i)
    n-⇒-elim : ∀ {ρ τ N M} → Neutral (⇒-elim ρ τ N M)
  
  mutual
    cr3 : ∀ {Γ} → (τ : Type) → (M : Term Γ) → Neutral M → ((M' : Term Γ) → Red M M' → TypeVal' Γ τ M') → TypeVal' Γ τ M
    cr3 (ρ ⇒ τ) M nM vrM = \U vU → lem ρ τ M nM vrM U vU (cr1 ρ U vU)
      where
        lem : ∀ {Γ} ρ τ → (M : Term Γ) → (nM : Neutral M) → (vrM : (M' : Term Γ) → Red M M' → TypeVal' Γ (ρ ⇒ τ) M') → (U : Term Γ) → TypeVal' Γ ρ U → SN U → TypeVal' Γ τ (⇒-elim ρ τ U M)
        lem ρ τ M nM vrM U vU (mkSN sU) = cr3 τ (⇒-elim ρ τ U M) n-⇒-elim \K → \
          { (⇒-elim-N-red {N' = U'} M r) → lem ρ τ M nM vrM U' (cr2 ρ U U' r vU) (sU U' r)
          ; (⇒-elim-M-red {M' = M'} N r) → vrM M' r U vU
          }
    cr3 Nat M nM vrM = mkSN vrM
    
    cr1 : ∀ {Γ} → (τ : Type) → (M : Term Γ) → TypeVal' Γ τ M → SN M
    cr1 {Γ} (ρ ⇒ τ) M vM = {!lem ρ τ $0 (tsucc ρ M) (cr1 τ (⇒-elim ρ τ $0 (tsucc ρ M)) (vM $0 (cr3 ρ $0 n-var (\M' ()))))!}
      where
        $0 : Term (ρ ∷ Γ)
        $0 = var here

        lem : ∀ {Γ} ρ τ → (N M : Term Γ) → SN (⇒-elim ρ τ N M) → SN M
        lem ρ τ N M (mkSN s) = mkSN \M' r → lem ρ τ N M' (s (⇒-elim ρ τ N M') (⇒-elim-M-red N r))
    cr1 Nat M sM = sM

  neutral-prepend : ∀ {Γ} Ω → (M : Term Γ) → Neutral M → Neutral (prepend Ω M)
  neutral-prepend = {!!}
  
  mutual
    cr3' : ∀ {Γ} → (τ : Type) → (M : Term Γ) → Neutral M → ((M' : Term Γ) → Red M M' → TypeVal'' Γ τ M') → TypeVal'' Γ τ M
    cr3' {Γ} (ρ ⇒ τ) M nM vrM = \Ω U vU → lem Ω U vU (cr1' ρ U vU)
      where
        lem : (Ω : Context) → (U : Term (Ω ++ Γ)) → TypeVal'' (Ω ++ Γ) ρ U → SN U → TypeVal'' (Ω ++ Γ) τ (⇒-elim ρ τ U (prepend Ω M))
        lem Ω U vU (mkSN sU) with prepend Ω M | neutral-prepend Ω M
        ... | M* | nM* = cr3' τ (⇒-elim ρ τ U (prepend Ω M)) n-⇒-elim \K → {!\
          { (⇒-elim-N-red {N' = U'} M r) → lem Ω U' (cr2' ρ U U' r vU) (sU U' r)
          ; (⇒-elim-M-red {M' = M'} N r) → {!vrM M' r U vU!}
          }!}
    cr3' Nat M nM vrM = mkSN vrM
    
    cr1' : ∀ {Γ} → (τ : Type) → (M : Term Γ) → TypeVal'' Γ τ M → SN M
    cr1' {Γ} (ρ ⇒ τ) M vM = {!lem ρ τ $0 (tsucc ρ M) (cr1' τ (⇒-elim ρ τ $0 (tsucc ρ M)) (vM $0 (cr3' ρ $0 n-var (\M' ()))))!}
      where
        $0 : Term (ρ ∷ Γ)
        $0 = var here

        lem : ∀ {Γ} ρ τ → (N M : Term Γ) → SN (⇒-elim ρ τ N M) → SN M
        lem ρ τ N M (mkSN s) = mkSN \M' r → lem ρ τ N M' (s (⇒-elim ρ τ N M') (⇒-elim-M-red N r))
    cr1' Nat M sM = sM

  data ContextVal' (Δ : Context) : (Γ : Context) → (γ : Subst Γ Δ) → Set where
    ε : ContextVal' Δ ε ε
    _∷_ : ∀ {Γ γ τ} {M : Term Δ} → TypeVal' Δ τ M → ContextVal' Δ Γ γ → ContextVal' Δ (τ ∷ Γ) (M ∷ γ)
  
  Vvar : ∀ Γ τ i → TypeVal' Γ τ (var i)
  Vvar Γ τ i = cr3 _ _ n-var (\M ())

  Vmapsucc : ∀ {Γ ρ τ M} → TypeVal' Γ τ M → TypeVal' (ρ ∷ Γ) τ (tsucc ρ M)
  Vmapsucc = {!!}

  CVmapsucc : ∀ {Γ Δ} → (ρ : Type) → (γ : Subst Γ Δ) → ContextVal' Δ Γ γ → ContextVal' (ρ ∷ Δ) Γ (up ρ γ)
  CVmapsucc ρ ε ε = ε
  CVmapsucc ρ (M ∷ γ) (vM ∷ vγ) = Vmapsucc vM ∷ CVmapsucc ρ γ vγ

  CVid : (Γ : Context) → ContextVal' Γ Γ (identity Γ)
  CVid ε = ε
  CVid (ρ ∷ Γ) = Vvar (ρ ∷ Γ) ρ here ∷ CVmapsucc ρ (identity Γ) (CVid Γ)

{-
  lem1 : (Γ : Context) → (ρ τ : Type) → (M : Term (ρ ∷ Γ))
       -- → ((U : Term) → TypeVal' ρ U → TypeVal' τ (subst U M))
       → ((Δ : Context) → (γ : Subst (ρ ∷ Γ) Δ) → ContextVal' Δ (ρ ∷ Γ) γ → TypeVal' Δ τ (bind γ M))
       → SN M
       --→ ((U : Term) → TypeVal' ρ U → SN (subst U M))
       → (Δ : Context) → (γ : Subst Γ Δ)
       → (N : Term Δ) → (TypeVal' Δ ρ N) → SN N
       --→ SN (subst N M)
       → (K : Term Δ) → Red (⇒-elim ρ τ N (⇒-intr ρ τ (bind (skip ρ γ) M))) K
       → TypeVal' Δ τ K
  lem1 Γ ρ τ M vsM sM Δ γ N vN sN _ (⇒-elim-red _ _) = {!vsM (N ∷ ε) (vN ∷ ε Γ)!}
  lem1 Γ ρ τ M vsM sM Δ γ N vN (mkSN sN) .(⇒-elim ρ τ N' (⇒-intr ρ τ _)) (⇒-elim-N-red {N' = N'} _ r)
    = cr3 τ _ n-⇒-elim (\K' r' → lem1 Γ ρ τ M vsM sM Δ γ N' vN' (sN N' r) K' r')
    where
      vN' : TypeVal' Δ ρ N'
      vN' = cr2 ρ N N' r vN
  lem1 Γ ρ τ M vsM (mkSN sM) Δ γ N vN sN .(⇒-elim ρ τ N (⇒-intr ρ τ _)) (⇒-elim-M-red _ (⇒-intr-red {M' = M'} r))
    -- = cr3 τ _ n-⇒-elim (\K' r' → lem1 Γ ρ τ M' {!(\U vU → cr2 τ (subst U M) (subst U M') (lem-subst-red (U ∷ ε) r) {!vsM U vU!} )!} (sM M' r) N vN sN K' r')
    = cr3 τ _ n-⇒-elim (\K' r' → {!!})

  abs-lem : (Γ : Context) → (ρ τ : Type)
          → (M : Term (ρ ∷ Γ) {-τ-})
          -- → ((U : Term{-ρ-}) → (vU : TypeVal' ρ U) → TypeVal' τ (subst U M))
          → ((Δ : Context) → (γ : Subst (ρ ∷ Γ) Δ)
          → (vγ : ContextVal' Δ (ρ ∷ Γ) γ) → TypeVal' Δ τ (bind γ M))
          → (Δ : Context) → (γ : Subst Γ Δ) → (N : Term Δ) → (vN : TypeVal' Δ ρ N) → TypeVal' Δ τ (⇒-elim ρ τ N (⇒-intr ρ τ (bind (skip ρ γ) M)))
  abs-lem Γ ρ τ M vsM Δ γ N vN = cr3 τ (⇒-elim ρ τ N (⇒-intr ρ τ (bind (skip ρ γ) M))) n-⇒-elim \K r → {!lem1 Γ ρ τ M vsM sM N vN sN K r !}
    where
      sM : SN M
      sM = cr1 τ M {!vsM!}
      -- sM = cr1 τ M (transport (TypeVal' τ) {!!} (vsM $0 (Vvar ρ zero)))
      -- where $0 = var here
  
      sN : SN N
      sN = cr1 ρ N vN
      -}
  
  lem1' : (Γ : Context) → (ρ τ : Type)
        → (M : Term (ρ ∷ Γ))
        → ((U : Term Γ) → TypeVal' Γ ρ U → TypeVal' Γ τ (subst ρ U M))
        → SN M
        → (N : Term Γ) → (vN : TypeVal' Γ ρ N) → SN N
        → (K : Term Γ) → Red (⇒-elim ρ τ N (⇒-intr ρ τ M)) K
        → TypeVal' Γ τ K
  lem1' Γ ρ τ M vsM sM N vN sN _ (⇒-elim-red _ _) = vsM N vN
  lem1' Γ ρ τ M vsM sM N vN (mkSN sN) .(⇒-elim ρ τ N' (⇒-intr ρ τ _)) (⇒-elim-N-red {N' = N'} _ r)
    = cr3 τ _ n-⇒-elim (\K' r' → lem1' Γ ρ τ M vsM sM N' vN' (sN N' r) K' r')
    where
      vN' : TypeVal' Γ ρ N'
      vN' = cr2 ρ N N' r vN
  lem1' Γ ρ τ M vsM (mkSN sM) N vN sN .(⇒-elim ρ τ N (⇒-intr ρ τ _)) (⇒-elim-M-red _ (⇒-intr-red {M' = M'} r))
    -- = cr3 τ _ n-⇒-elim (\K' r' → lem1 Γ ρ τ M' {!(\U vU → cr2 τ (subst U M) (subst U M') (lem-subst-red (U ∷ ε) r) {!vsM U vU!} )!} (sM M' r) N vN sN K' r')
    = cr3 τ _ n-⇒-elim (\K' r' → lem1' Γ ρ τ M' vsM' (sM M' r) N vN sN K' r')
    where
      vsM' : (U : Term Γ) → (vU : TypeVal' Γ ρ U) → TypeVal' Γ τ (subst ρ U M')
      vsM' U vU = cr2 τ (subst ρ U M) (subst ρ U M') (lem-subst-red (set ρ U (identity Γ)) r) (vsM U vU)
      
  abs-lem' : (Γ : Context) → (ρ τ : Type)
          → (M : Term (ρ ∷ Γ) {-τ-})
          → TypeVal' (ρ ∷ Γ) τ M
          → ((U : Term Γ {-ρ-}) → (vU : TypeVal' Γ ρ U) → TypeVal' Γ τ (subst ρ U M))
          → (N : Term Γ) → (vN : TypeVal' Γ ρ N) → TypeVal' Γ τ (⇒-elim ρ τ N (⇒-intr ρ τ M))
  abs-lem' Γ ρ τ M vM vsM N vN = cr3 τ (⇒-elim ρ τ N (⇒-intr ρ τ M)) n-⇒-elim \K r → lem1' Γ ρ τ M vsM sM N vN sN K r 
    where
      sM : SN M
      sM = cr1 τ M vM
  
      sN : SN N
      sN = cr1 ρ N vN

  vtsucc : ∀ {Γ} → (ρ τ : Type) → (M : Term Γ) → TypeVal' Γ τ M → TypeVal' (ρ ∷ Γ) τ (tsucc ρ M)
  vtsucc ρ (τ ⇒ τ₁) M vM = \U vU → {!!}
  vtsucc ρ Nat M vM = {!!}

  vssucc : ∀ {Γ Δ} → (ρ : Type) → (γ : Subst Γ Δ) → ContextVal' Δ Γ γ → ContextVal' (ρ ∷ Δ) Γ (up ρ γ)
  vssucc ρ .ε ε = ε
  vssucc ρ .(_ ∷ _) (vM ∷ vγ) = vtsucc ρ _ _ vM ∷ (vssucc ρ _ vγ)

  vskip : ∀ {Γ Δ} → (ρ : Type) → (γ : Subst Γ Δ) → ContextVal' Δ Γ γ → ContextVal' (ρ ∷ Δ) (ρ ∷ Γ) (skip ρ γ)
  vskip ρ γ vγ = Vvar (ρ ∷ _) ρ here ∷ {!!}
  
  TermVal' : (Γ : Context) → {τ : Type} → {M : Term Γ} → Valid Γ τ M → {Δ : Context} → (γ : Subst Γ Δ) → ContextVal' Δ Γ γ → TypeVal' Δ τ (bind γ M)
  TermVal' ε (#var () τ h) ε ε
  TermVal' _ (#var here τ here) (M ∷ γ) (vM ∷ vγ) = vM
  TermVal' _ (#var (there i) τ (there h)) (_ ∷ γ) (_ ∷ vγ) = TermVal' _ (#var i τ h) γ vγ
  -- TermVal' Γ (#⇒-intr ρ τ M #M) γ vγ = \N vN → abs-lem Γ ρ τ M (\Δ' γ' vγ' → TermVal' (ρ ∷ Γ) #M γ' vγ') _ γ N vN 
  TermVal' Γ (#⇒-intr ρ τ M #M) {Δ} γ vγ = \N vN → abs-lem' Δ ρ τ (bind (skip ρ γ) M) (TermVal' (ρ ∷ Γ) #M (skip ρ γ) (vskip ρ γ vγ)) (\U vU → {!TermVal' (ρ ∷ Γ) #M (set ρ U γ) (vU ∷ vγ) !}) N vN 
  TermVal' Γ (#⇒-elim ρ τ N #N M #M) γ vγ = TermVal' Γ #M γ vγ (bind γ N) (TermVal' Γ #N γ vγ)
  TermVal' Γ #N-zero γ vγ = sn-zero
  TermVal' Γ (#N-succ M #M) γ vγ = sn-succ (bind γ M) (TermVal' Γ #M γ vγ)
  TermVal' Γ (#N-elim ρ N₀ #N₀ Nₛ #Nₛ M #M) γ vγ = {!TermVal' Γ #M γ vγ!}


sn : (Γ : Context) → (τ : Type) → (M : Term Γ) → Valid Γ τ M → SN M
sn Γ τ M #M = cr1 τ M (transport (TypeVal' Γ τ) {!lem-bind-identity Γ M!} (TermVal' Γ #M (identity Γ) (CVid Γ)))
