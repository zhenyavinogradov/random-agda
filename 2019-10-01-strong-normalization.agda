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

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,,_
    field
      first : A
      second : B first

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
  infix 4 _≤_
  data _≤_ : (Γ Δ : Context) → Set where
    nil : ε ≤ ε
    match : ∀ {Γ Δ} → (ρ : Type) → Γ ≤ Δ → ρ ∷ Γ ≤ ρ ∷ Δ
    pass : ∀ {Γ Δ} → (ρ : Type) → Γ ≤ Δ → Γ ≤ ρ ∷ Δ

  ElemF TermF Subst TermK : (Γ Δ : Context) → Set
  ElemF Γ Δ = Elem Γ → Elem Δ
  TermK Γ Δ = Elem Γ → Term Δ
  Subst Γ Δ = All (\ρ → Term Δ) Γ
  TermF Γ Δ = Term Γ → Term Δ

  SubstF : (Ω : Context) → (Γ Δ : Context) → Set
  SubstF Ω Γ Δ = Subst Ω Γ → Subst Ω Δ


  Identity : (F : Context → Context → Set) → Set
  Identity F = (Γ : Context) → F Γ Γ

  Compose : (F : Context → Context → Set) → Set
  Compose F = ∀ {Γ Δ Ω} → F Δ Ω → F Γ Δ → F Γ Ω

  Up : (F : Context → Context → Set) → Set
  Up F = ∀ {Γ} → (ρ : Type) → F Γ (ρ ∷ Γ)

  -- Add : (F : Context → Context → Set) → Set
  -- Add F = ∀ {Γ Δ} → (ρ : Type) → Term Δ → F Γ Δ → F (ρ ∷ Γ) Δ

  Skip : (F : Context → Context → Set) → Set
  Skip F = ∀ {Γ Δ} → (ρ : Type) → F Γ Δ → F (ρ ∷ Γ) (ρ ∷ Δ)


  idExt : Identity _≤_
  idExt ε = nil
  idExt (ρ ∷ Γ) = match ρ (idExt Γ)

  composeExt : Compose _≤_
  composeExt nil ex₂ = ex₂
  composeExt (match ρ ex₁) (match .ρ ex₂) = match ρ (composeExt ex₁ ex₂)
  composeExt (match ρ ex₁) (pass .ρ ex₂) = pass ρ (composeExt ex₁ ex₂)
  composeExt (pass ρ ex₁) ex₂ = pass ρ (composeExt ex₁ ex₂)


  idSubst : Identity Subst
  idSubst Γ = {!!}

  composeSubst : Compose Subst
  composeSubst γ₁ γ₂ = {!!}



  _⇛_ : (F G : Context → Context → Set) → Set
  F ⇛ G = ∀ {Γ Δ} → F Γ Δ → G Γ Δ


  skipExt : Skip _≤_
  skipExt = match

  skipElemF : Skip ElemF
  skipElemF ρ f = \{ here → here ; (there i) → there (f i) }

  skipTermK : Skip TermK
  skipTermK ρ f = \{ here → var here ; (there i) → {!f i!} }


  fsucc : ∀ {Γ Δ} → (ρ : Type) → (Elem Γ → Elem Δ) → (Elem (ρ ∷ Γ) → Elem (ρ ∷ Δ))
  fsucc = skipElemF

  up* : ∀ {Γ Δ} → (Ω : Context) → Subst Γ Δ → Subst Γ (Ω ++ Δ)
  up* Ω γ = {!!}
  
  set : ∀ {Γ Δ} → (ρ : Type) → Term Δ → Subst Γ Δ → Subst (ρ ∷ Γ) Δ
  set ρ U γ = U ∷ γ

  up : ∀ {Γ Δ} → (ρ : Type) → Subst Γ Δ → Subst Γ (ρ ∷ Δ)
  up ρ γ = up* (single ρ) γ

  Ext⇒ElemF : _≤_ ⇛ ElemF
  Ext⇒ElemF (match ρ ex) here = here
  Ext⇒ElemF (match ρ ex) (there i) = there (Ext⇒ElemF ex i)
  Ext⇒ElemF (pass ρ ex) i = there (Ext⇒ElemF ex i)

  ElemF⇛TermK : ElemF ⇛ TermK
  ElemF⇛TermK f i = var (f i)

  TermK⇛TermF : TermK ⇛ TermF
  TermK⇛TermF f (var i) = f i
  TermK⇛TermF f (⇒-intr ρ τ M) = ⇒-intr ρ τ (TermK⇛TermF (skipTermK ρ f) M)
  TermK⇛TermF f (⇒-elim ρ τ N M) = ⇒-elim ρ τ (TermK⇛TermF f N) (TermK⇛TermF f M)
  TermK⇛TermF f (N-elim ρ N₀ Nₛ M) = N-elim ρ (TermK⇛TermF f N₀) (TermK⇛TermF (skipTermK ρ f) Nₛ) (TermK⇛TermF f M)
  TermK⇛TermF f N-zero = N-zero
  TermK⇛TermF f (N-succ M) = N-succ (TermK⇛TermF f M)

  Subst⇛TermK : Subst ⇛ TermK
  Subst⇛TermK (U ∷ γ) here = U
  Subst⇛TermK (U ∷ γ) (there i) = Subst⇛TermK γ i

  skipSubst : Skip Subst
  skipSubst ρ γ = var here ∷ {!TermF⇛SubstF (ElemF⇛TermF ?) γ!}

  Subst⇛TermF : Subst ⇛ TermF
  Subst⇛TermF γ (var i) = Subst⇛TermK γ i
  Subst⇛TermF γ (⇒-intr ρ τ M) = ⇒-intr ρ τ (Subst⇛TermF (skipSubst ρ γ) M)
  Subst⇛TermF γ (⇒-elim ρ τ N M) = ⇒-elim ρ τ (Subst⇛TermF γ N) (Subst⇛TermF γ M)
  Subst⇛TermF γ (N-elim ρ N₀ Nₛ M) = N-elim ρ (Subst⇛TermF γ N₀) (Subst⇛TermF (skipSubst ρ γ) Nₛ) (Subst⇛TermF γ M)
  Subst⇛TermF γ N-zero = N-zero
  Subst⇛TermF γ (N-succ M) = N-succ (Subst⇛TermF γ M)

  TermK⇛Subst : TermK ⇛ Subst
  TermK⇛Subst {ε} f = ε
  TermK⇛Subst {_ ∷ Γ} f = f here ∷ TermK⇛Subst (\i → f (there i))

  TermF⇛SubstF : ∀ {Ω} → TermF ⇛ SubstF Ω
  TermF⇛SubstF f γ = mapAll f γ

  ElemF⇛TermF : ElemF ⇛ TermF
  ElemF⇛TermF f = TermK⇛TermF (ElemF⇛TermK f)

  Ext⇛Subst : _≤_ ⇛ Subst
  Ext⇛Subst nil = ε
  Ext⇛Subst (match ρ ex) = var here ∷ TermF⇛SubstF (ElemF⇛TermF there) (Ext⇛Subst ex)
  Ext⇛Subst (pass ρ ex) = TermF⇛SubstF (ElemF⇛TermF there) (Ext⇛Subst ex)

  
  mapTerm : ∀ {Γ Δ} → (Elem Γ → Elem Δ) → (Term Γ → Term Δ)
  mapTerm = ElemF⇛TermF

  mapSubst : ∀ {Γ Δ Δ'} → (Term Δ → Term Δ') → Subst Γ Δ → Subst Γ Δ'
  mapSubst = TermF⇛SubstF

  ext : ∀ {Γ Δ} → Γ ≤ Δ → Subst Γ Δ
  ext = Ext⇛Subst

  buildSubst : ∀ {Γ Δ} → (Elem Γ → Term Δ) → Subst Γ Δ
  buildSubst = TermK⇛Subst

  applySubst : ∀ {Γ Δ} → Subst Γ Δ → Elem Γ → Term Δ
  applySubst = Subst⇛TermK


  skip : ∀ {Γ Δ} → (ρ : Type) → Subst Γ Δ → Subst (ρ ∷ Γ) (ρ ∷ Δ)
  -- skip ρ γ = set ρ (var here) (up ρ γ)
  skip = skipSubst

  identity : (Γ : Context) → Subst Γ Γ
  identity = idSubst

  up' : ∀ {Γ} → (ρ : Type) → Subst Γ (ρ ∷ Γ)
  up' ρ = {!!}


  up*s : ∀ {Γ} → (Ω : Context) → Subst Γ (Ω ++ Γ)
  up*s Ω = buildSubst (\i → var (elemr Ω i))
  
  bind : {Γ Δ : Context} → Subst Γ Δ → Term Γ → Term Δ
  bind = Subst⇛TermF

  fish : ∀ {Γ Δ Ω} → Subst Δ Ω → Subst Γ Δ → Subst Γ Ω
  fish γ₁ γ₂ = mapSubst (bind γ₁) γ₂

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

  record RedTerm {Γ : Context} (M : Term Γ) : Set where
    constructor mkRedTerm
    field
      term : Term Γ
      red : Red M term

  ⇒-elim-red' : ∀ {Γ Δ} → (γ : Subst Γ Δ) → ∀ {ρ τ} N M → Red (bind γ (⇒-elim ρ τ N (⇒-intr ρ τ M))) (bind (set ρ (bind γ N) γ) M)
  ⇒-elim-red' γ {ρ = ρ} N M = {!⇒-elim-red (bind γ N) (bind (skip ρ γ) M)!}
  
  lem-subst-red : ∀ {Γ Δ} → (γ : Subst Γ Δ) → {M M' : Term Γ} → Red M M' → Red (bind γ M) (bind γ M')
  lem-subst-red γ r = {!⇒-elim-red' γ N M!}


-- SN
module _ where
  data SN {Γ : Context} (M : Term Γ) : Set where
    mkSN : ((M' : Term Γ) → Red M M' → SN M') → SN M
  
  sn-zero : ∀ {Γ} → SN {Γ} N-zero
  sn-zero = mkSN \_ ()
  
  sn-succ : ∀ {Γ} → (M : Term Γ) → SN M → SN (N-succ M)
  sn-succ M (mkSN sM) = mkSN (\_ → \{ (N-succ-red {M' = M'} r) → sn-succ M' (sM M' r)})
  
  sn-⇒-intr : ∀ {Γ ρ τ} → (M : Term (ρ ∷ Γ)) → SN M → SN (⇒-intr ρ τ M)
  sn-⇒-intr M (mkSN sM) = mkSN (\_ → \{ (⇒-intr-red {M' = M'} r) → sn-⇒-intr M' (sM M' r)})


-- Val
module _ where
  data Neutral {Γ} : Term Γ → Set where
    n-var : ∀ {i} → Neutral (var i)
    n-⇒-elim : ∀ {ρ τ N M} → Neutral (⇒-elim ρ τ N M)

  extendTerm : ∀ {Γ Γ'} → (ex : Γ ≤ Γ') → Term Γ → Term Γ'
  extendTerm ex = bind (ext ex)

  extendSubst : ∀ {Γ Δ Δ'} → (ex : Δ ≤ Δ') → Subst Γ Δ → Subst Γ Δ'
  extendSubst = {!!}

  extendRed : ∀ {Γ Γ' M M'} → (ex : Γ ≤ Γ') → Red M M' → Red (extendTerm ex M) (extendTerm ex M')
  extendRed = {!!}

  extendRedTerm : ∀ {Γ Γ' M} → (ex : Γ ≤ Γ') → RedTerm M → RedTerm (extendTerm ex M)
  extendRedTerm ex (mkRedTerm M r) = mkRedTerm (extendTerm ex M) (extendRed ex r)

  unextendRedTerm : ∀ {Γ Γ' M} → (ex : Γ ≤ Γ') → RedTerm (extendTerm ex M) → RedTerm M
  unextendRedTerm = {!!}

  extendSN : ∀ {Γ Γ' M} → (ex : Γ ≤ Γ') → SN M → SN (extendTerm ex M)
  extendSN = {!!}

  unextendSN : ∀ {Γ Γ' M} → (ex : Γ ≤ Γ') → SN (extendTerm ex M) → SN M
  unextendSN = {!!}

  extendNeutral : ∀ {Γ Γ' M} → (ex : Γ ≤ Γ') → Neutral M → Neutral (extendTerm ex M)
  extendNeutral = {!bind ?!}

  TypeVal' : (Γ : Context) → (τ : Type) → (M : Term Γ) → Set
  TypeVal' Γ (ρ ⇒ τ) M = (Γ' : Context) → (ex : Γ ≤ Γ') → (U : Term Γ') → TypeVal' Γ' ρ U → TypeVal' Γ' τ (⇒-elim ρ τ U (extendTerm ex M))
  TypeVal' Γ Nat M = SN M
  
  cr2 : ∀ {Γ} → (τ : Type) → (M M' : Term Γ) → Red M M' → TypeVal' Γ τ M → TypeVal' Γ τ M'
  cr2 (ρ ⇒ τ) M M' r vM = \Γ' ex N vN → cr2 τ _ _ (⇒-elim-M-red N (extendRed ex r)) (vM Γ' ex N vN)
  cr2 Nat M M' r (mkSN sM) = sM M' r
  
  mutual
    cr3 : ∀ {Γ} → (τ : Type) → (M : Term Γ) → Neutral M → ((M' : Term Γ) → Red M M' → TypeVal' Γ τ M') → TypeVal' Γ τ M
    cr3 {Γ} (ρ ⇒ τ) M nM vrM = \Γ' ex U vU → lem Γ' ex U vU (cr1 ρ U vU)
      where
        lem : (Γ' : Context) → (ex : Γ ≤ Γ') → (U : Term Γ') → TypeVal' Γ' ρ U → SN U → TypeVal' Γ' τ (⇒-elim ρ τ U (extendTerm ex M))
        lem Γ' ex U vU (mkSN sU) with extendTerm ex M | extendNeutral ex nM
        ... | M* | nM* = cr3 τ (⇒-elim ρ τ U M*) n-⇒-elim \K → \
          { (⇒-elim-N-red {N' = U'} M r) → {!lem Γ' ex U' (cr2 ρ U U' r vU) (sU U' r)!}
          ; (⇒-elim-M-red {M' = M*'} N r) → {!vrM!}
          }
    cr3 Nat M nM vrM = mkSN vrM
  
    Vvar' : ∀ Γ τ i → TypeVal' Γ τ (var i)
    Vvar' Γ τ i = cr3 _ _ n-var (\M ())
    
    cr1 : ∀ {Γ} → (τ : Type) → (M : Term Γ) → TypeVal' Γ τ M → SN M
    cr1 {Γ} (ρ ⇒ τ) M vM = unextendSN (pass ρ (idExt Γ)) (lem ρ τ $0 (extendTerm (pass ρ (idExt Γ)) M) (cr1 τ M0 vM0))
      where
        $0 : Term (ρ ∷ Γ)
        $0 = var here

        M0 : Term (ρ ∷ Γ)
        M0 = ⇒-elim ρ τ $0 (extendTerm (pass ρ (idExt Γ)) M)

        vM0 : TypeVal' (ρ ∷ Γ) τ M0
        vM0 = vM (ρ ∷ Γ) (pass ρ (idExt Γ)) $0 (Vvar' (ρ ∷ Γ) ρ here)

        lem : ∀ {Γ} ρ τ → (N M : Term Γ) → SN (⇒-elim ρ τ N M) → SN M
        lem ρ τ N M (mkSN s) = mkSN \M' r → lem ρ τ N M' (s (⇒-elim ρ τ N M') (⇒-elim-M-red N r))
    cr1 Nat M sM = sM

  abs-lem-lem : (Γ : Context) → (ρ τ : Type)
              → (M : Term (ρ ∷ Γ))
              → ((Γ' : Context) → (ex : Γ ≤ Γ') → (U : Term Γ') → (vU : TypeVal' Γ' ρ U) → TypeVal' Γ' τ (subst ρ U (extendTerm (match ρ ex) M)))
              → SN M
              → (Γ' : Context) → (ex : Γ ≤ Γ') → (N : Term Γ') → (vN : TypeVal' Γ' ρ N) → SN N
              → (K : Term Γ') → Red (⇒-elim ρ τ N (⇒-intr ρ τ (extendTerm (match ρ ex) M))) K
              → TypeVal' Γ' τ K
  abs-lem-lem Γ ρ τ M vsM sM Γ' ex N vN sN _ (⇒-elim-red _ _) = {!vsM Ω N vN!}
  abs-lem-lem Γ ρ τ M vsM sM Γ' ex N vN (mkSN sN) .(⇒-elim ρ τ N' (⇒-intr ρ τ _)) (⇒-elim-N-red {N' = N'} _ r)
    = cr3 τ _ n-⇒-elim (\K' r' → abs-lem-lem Γ ρ τ M vsM sM Γ' ex N' vN' (sN N' r) K' r')
    where
      vN' : TypeVal' Γ' ρ N'
      vN' = cr2 ρ N N' r vN
  abs-lem-lem Γ ρ τ M vsM (mkSN sM) Γ' ex N vN sN .(⇒-elim ρ τ N (⇒-intr ρ τ _)) (⇒-elim-M-red _ (⇒-intr-red {M' = M'} r))
    = cr3 τ _ n-⇒-elim (\K' r' → {!abs-lem-lem Γ ρ τ M' vsM' (sM M' r) N vN sN K' r'!})
    where
      vsM' : (Ω' : Context) → (U : Term (Ω' ++ Γ)) → (vU : TypeVal' (Ω' ++ Γ) ρ U) → TypeVal' (Ω' ++ Γ) τ (subst ρ U (bind (skip ρ (up*s Ω')) {!M'!}))
      vsM' Ω' U vU = {!cr2 τ (subst ρ U M) (subst ρ U M') (lem-subst-red (set ρ U (identity Γ)) r) (vsM U vU)!}
      
  abs-lem : (Γ : Context) → (ρ τ : Type)
          → (M : Term (ρ ∷ Γ))
          → TypeVal' (ρ ∷ Γ) τ M
          → ((Γ' : Context) → (ex : Γ ≤ Γ') → (U : Term Γ') → (vU : TypeVal' Γ' ρ U) → TypeVal' Γ' τ (subst ρ U (extendTerm (match ρ ex) M)))
          → (Γ' : Context) → (ex : Γ ≤ Γ') → (N : Term Γ') → (vN : TypeVal' Γ' ρ N) → TypeVal' Γ' τ (⇒-elim ρ τ N (⇒-intr ρ τ (extendTerm (match ρ ex) M)))
  abs-lem Γ ρ τ M vM vsM Γ' ex N vN = cr3 τ _ n-⇒-elim \K r → abs-lem-lem Γ ρ τ M vsM sM Γ' ex N vN sN K r 
    where
      sM : SN M
      sM = cr1 τ M vM
  
      sN : SN N
      sN = cr1 ρ N vN

  data ContextVal' (Δ : Context) : (Γ : Context) → (γ : Subst Γ Δ) → Set where
    ε : ContextVal' Δ ε ε
    _∷_ : ∀ {Γ γ τ} {M : Term Δ} → TypeVal' Δ τ M → ContextVal' Δ Γ γ → ContextVal' Δ (τ ∷ Γ) (M ∷ γ)

  extendTypeVal : ∀ {Γ Γ' τ M} → (ex : Γ ≤ Γ') → TypeVal' Γ τ M → TypeVal' Γ' τ (extendTerm ex M)
  extendTypeVal {τ = ρ ⇒ τ} ex vM = \Γ' ex U vU → {!vM (Ω' ++ Ω) !}
  extendTypeVal {τ = Nat} ex sM = extendSN ex sM

  extendContextVal : ∀ {Γ Δ Δ' γ} → (ex : Δ ≤ Δ') → ContextVal' Δ Γ γ → ContextVal' Δ' Γ (extendSubst ex γ)
  extendContextVal = {!!}
  
  TermVal' : (Γ : Context) → {τ : Type} → {M : Term Γ} → Valid Γ τ M → {Δ : Context} → (γ : Subst Γ Δ) → ContextVal' Δ Γ γ → TypeVal' Δ τ (bind γ M)
  TermVal' ε (#var () τ h) ε ε
  TermVal' _ (#var here τ here) (M ∷ γ) (vM ∷ vγ) = vM
  TermVal' _ (#var (there i) τ (there h)) (_ ∷ γ) (_ ∷ vγ) = TermVal' _ (#var i τ h) γ vγ
  TermVal' Γ (#⇒-intr ρ τ M #M) {Δ} γ vγ = \Γ' ex U vU → {!abs-lem Δ ρ τ (bind (skip ρ γ) M)!}
  TermVal' Γ (#⇒-elim ρ τ N #N M #M) {Δ} γ vγ = {!TermVal' Γ #M γ vγ Δ (idExt Δ) (bind γ N) (TermVal' Γ #N γ vγ)!}
  TermVal' Γ #N-zero γ vγ = sn-zero
  TermVal' Γ (#N-succ M #M) γ vγ = sn-succ (bind γ M) (TermVal' Γ #M γ vγ)
  TermVal' Γ (#N-elim ρ N₀ #N₀ Nₛ #Nₛ M #M) γ vγ = {!TermVal'' Γ #M γ vγ!}
