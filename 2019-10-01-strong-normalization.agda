module _ where

-- lib
module _ where
  record ⊤ : Set where
    constructor tt

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

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data Elem {A : Set} : List A → Set where
    here : ∀ {a as} → Elem (a ∷ as)
    there : ∀ {a as} → Elem as → Elem (a ∷ as)

  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a
  {-# BUILTIN EQUALITY _≡_ #-}

  transport : {A : Set} → (P : A → Set) → {a a' : A} → a ≡ a' → P a → P a'
  transport P refl Pa = Pa


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

  ElemF TermF TermK : (Γ Δ : Context) → Set
  ElemF Γ Δ = Elem Γ → Elem Δ
  TermK Γ Δ = Elem Γ → Term Δ
  TermF Γ Δ = Term Γ → Term Δ

  Identity Compose : (F : (Γ Δ : Context) → Set) → Set
  Identity F = ∀ {Γ} → F Γ Γ
  Compose F = ∀ {Γ Δ Ω} → F Δ Ω → F Γ Δ → F Γ Ω

  Skip : (F : (Γ Δ : Context) → Set) → Set
  Skip F = ∀ {Γ Δ} → (ρ : Type) → F Γ Δ → F (ρ ∷ Γ) (ρ ∷ Δ)

  _⇛_ : (F G : (Γ Δ : Context) → Set) → Set
  F ⇛ G = ∀ {Γ Δ} → F Γ Δ → G Γ Δ


  idExt : Identity _≤_
  idExt {ε} = nil
  idExt {ρ ∷ Γ} = match ρ (idExt {Γ})

  idElemF : Identity ElemF
  idElemF i = i

  idTermK : Identity TermK
  idTermK i = var i

  idTermF : Identity TermF
  idTermF i = i

  composeExt : Compose _≤_
  composeExt nil β = β
  composeExt (match ρ α) (match .ρ β) = match ρ (composeExt α β)
  composeExt (match ρ α) (pass .ρ β) = pass ρ (composeExt α β)
  composeExt (pass ρ α) β = pass ρ (composeExt α β)

  composeElemF : Compose ElemF
  composeElemF f g i = f (g i)

  composeTermF : Compose TermF
  composeTermF f g M = f (g M)

  Ext⇛ElemF : _≤_ ⇛ ElemF
  Ext⇛ElemF (match ρ α) here = here
  Ext⇛ElemF (match ρ α) (there i) = there (Ext⇛ElemF α i)
  Ext⇛ElemF (pass ρ α) i = there (Ext⇛ElemF α i)

  ElemF⇛TermK : ElemF ⇛ TermK
  ElemF⇛TermK f i = idTermK (f i)

  skipElemF : Skip ElemF
  skipElemF ρ f = \{ here → here ; (there i) → there (f i) }

  ElemF⇛TermF : ElemF ⇛ TermF
  ElemF⇛TermF f (var i) = var (f i)
  ElemF⇛TermF f (⇒-intr ρ τ M) = ⇒-intr ρ τ (ElemF⇛TermF (skipElemF ρ f) M)
  ElemF⇛TermF f (⇒-elim ρ τ N M) = ⇒-elim ρ τ (ElemF⇛TermF f N) (ElemF⇛TermF f M)
  ElemF⇛TermF f (N-elim ρ N₀ Nₛ M) = N-elim ρ (ElemF⇛TermF f N₀) (ElemF⇛TermF (skipElemF ρ f) Nₛ) (ElemF⇛TermF f M)
  ElemF⇛TermF f N-zero = N-zero
  ElemF⇛TermF f (N-succ M) = N-succ (ElemF⇛TermF f M)

  skipTermK : Skip TermK
  skipTermK ρ f = \{ here → var here ; (there i) → ElemF⇛TermF there (f i) }

  TermK⇛TermF : TermK ⇛ TermF
  TermK⇛TermF f (var i) = f i
  TermK⇛TermF f (⇒-intr ρ τ M) = ⇒-intr ρ τ (TermK⇛TermF (skipTermK ρ f) M)
  TermK⇛TermF f (⇒-elim ρ τ N M) = ⇒-elim ρ τ (TermK⇛TermF f N) (TermK⇛TermF f M)
  TermK⇛TermF f (N-elim ρ N₀ Nₛ M) = N-elim ρ (TermK⇛TermF f N₀) (TermK⇛TermF (skipTermK ρ f) Nₛ) (TermK⇛TermF f M)
  TermK⇛TermF f N-zero = N-zero
  TermK⇛TermF f (N-succ M) = N-succ (TermK⇛TermF f M)
  
  composeTermK : Compose TermK
  composeTermK γ₁ γ₂ i = (TermK⇛TermF γ₁) (γ₂ i)

  Ext⇛TermK : _≤_ ⇛ TermK
  Ext⇛TermK α = ElemF⇛TermK (Ext⇛ElemF α)

  Ext⇛TermF : _≤_ ⇛ TermF
  Ext⇛TermF α = TermK⇛TermF (Ext⇛TermK α)


  set : ∀ {Γ Δ} → (ρ : Type) → (U : Term Δ) → (γ : TermK Γ Δ) → TermK (ρ ∷ Γ) Δ
  set ρ U γ = \{ here → U ; (there i) → γ i }

  skip : ∀ {Γ Δ} → (ρ : Type) → (γ : TermK Γ Δ) → TermK (ρ ∷ Γ) (ρ ∷ Δ)
  skip ρ γ = set ρ (var here) (composeTermK (Ext⇛TermK (pass ρ idExt)) γ)


  bind : {Γ Δ : Context} → TermK Γ Δ → Term Γ → Term Δ
  bind = TermK⇛TermF

  subst : ∀ {Γ} → (ρ : Type) → Term Γ → Term (ρ ∷ Γ) → Term Γ
  subst {Γ} ρ N M = bind (set ρ N idTermK) M


  Eq : (F : (Γ Δ : Context) → Set) → Set₁
  Eq F = ∀ {Γ Δ} → F Γ Δ → F Γ Δ → Set

  EqElemF : Eq ElemF
  EqElemF f f' = ∀ i → f i ≡ f' i

  EqTermK : Eq TermK
  EqTermK f f' = ∀ i → f i ≡ f' i

  EqTermF : Eq TermF
  EqTermF f f' = ∀ M → f M ≡ f' M


module _ where
  data Var : Set where
    $ : ℕ → Var

  data Term* : Set where
    var : (τ : Type) → Var → Term*
    --llet : (ρ τ : Type) → (x : Var) → Term*{-ρ-} → Term*{-x:ρ⊢τ-} → Term*{-τ-}
  
    ⇒-intr : (ρ τ : Type) → Term* → Term*
    ⇒-elim : (ρ τ : Type) → Term* → Term* → Term*
  
    N-elim : (ρ : Type) → Term* → Term* → Term* → Term*
    N-zero : Term*
    N-succ : Term* → Term*

  data Naming (Γ : Context) : Term* → Set where
    -- %var : (τ : Type) → (i : Elem Γ) → Has Γ i τ → Naming Γ (var τ i)
    %⇒-intr : ∀ ρ τ M → Naming (ρ ∷ Γ) M → Naming Γ (⇒-intr ρ τ M)
    %⇒-elim : ∀ ρ τ N M → Naming Γ N → Naming Γ M → Naming Γ (⇒-elim ρ τ N M)


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

  bindRed : ∀ {Γ Δ} → (γ : TermK Γ Δ) → {M M' : Term Γ} → Red M M' → Red (bind γ M) (bind γ M')
  bindRed γ (⇒-elim-red {ρ = ρ} N M) = transport (\z → Red (bind γ (⇒-elim _ _ N (⇒-intr _ _ M))) z) (elem1 M) (⇒-elim-red (TermK⇛TermF γ N) (TermK⇛TermF (skipTermK _ γ) M))
    where
      elem1 : EqTermF (composeTermF (TermK⇛TermF (set ρ (TermK⇛TermF γ N) idTermK)) (TermK⇛TermF (skipTermK ρ γ))) (composeTermF (TermK⇛TermF γ) (TermK⇛TermF (set ρ N idTermK)))
      elem1 = {!!}
  bindRed γ (N-elim-zero-red {ρ = ρ} N₀ Nₛ) = N-elim-zero-red (TermK⇛TermF γ N₀) (TermK⇛TermF (skipTermK ρ γ) Nₛ )
  bindRed γ (N-elim-succ-red {ρ = ρ} N₀ Nₛ M) = transport (\z → Red (bind γ (N-elim ρ N₀ Nₛ (N-succ M))) z) (elem1 M) (N-elim-succ-red (TermK⇛TermF γ N₀) (TermK⇛TermF (skipTermK ρ γ) Nₛ) (TermK⇛TermF γ M))
    where
      elem1 : ∀ M → subst ρ (N-elim ρ (TermK⇛TermF γ N₀) (TermK⇛TermF (skipTermK ρ γ) Nₛ) (TermK⇛TermF γ M)) (TermK⇛TermF (skipTermK ρ γ) Nₛ) ≡ bind γ (subst ρ (N-elim ρ N₀ Nₛ M) Nₛ)
      elem1 = {!!}
  bindRed γ (⇒-intr-red {ρ = ρ} r) = ⇒-intr-red (bindRed (skipTermK ρ γ) r)
  bindRed γ (⇒-elim-N-red M r) = ⇒-elim-N-red (TermK⇛TermF γ M) (bindRed γ r)
  bindRed γ (⇒-elim-M-red N r) = ⇒-elim-M-red (TermK⇛TermF γ N) (bindRed γ r)
  bindRed γ (N-succ-red r) = N-succ-red (bindRed γ r)


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

  extendTerm : ∀ {Γ Γ'} → (α : Γ ≤ Γ') → Term Γ → Term Γ'
  extendTerm α = bind (Ext⇛TermK α)

  extendTermK : ∀ {Γ Δ Δ'} → (α : Δ ≤ Δ') → TermK Γ Δ → TermK Γ Δ'
  extendTermK α γ = composeTermK (Ext⇛TermK α) γ

  extendRed : ∀ {Γ Γ' M M'} → (α : Γ ≤ Γ') → Red M M' → Red (extendTerm α M) (extendTerm α M')
  extendRed α = bindRed (Ext⇛TermK α)

  extendRedTerm : ∀ {Γ Γ'} → (α : Γ ≤ Γ') → (M : Term Γ) → RedTerm M → RedTerm (extendTerm α M)
  extendRedTerm α M (mkRedTerm M' r) = mkRedTerm (extendTerm α M') (extendRed α r)

  -- lem-extend-subst : ∀ {Γ Γ'} → (α : Γ ≤ Γ') → (ρ : Type) → (N : Term Γ) → (M : Term (ρ ∷ Γ)) → extendTerm ex (subst ρ N M) ≡ subst ρ (extendTerm ex N) (extendTerm (match ρ ex) M)
  lem-extend-subst : ∀ {Γ Γ'} → (α : Γ ≤ Γ') → (ρ : Type) → (N : Term Γ)
                   → EqTermF (composeTermF (Ext⇛TermF α) (TermK⇛TermF (set ρ N idTermK))) (TermK⇛TermF (composeTermK (set ρ (Ext⇛TermF α N) idTermK) (Ext⇛TermK (match ρ α))))
  lem-extend-subst = {!!}

  unextendRedTerm : ∀ {Γ Γ'} → (α : Γ ≤ Γ') → (M : Term Γ) → RedTerm (extendTerm α M) → RedTerm M
  unextendRedTerm α M (mkRedTerm term red) with extendTerm α M | red
  … | .(⇒-elim _ _ N (⇒-intr _ _ M₁)) | ⇒-elim-red N M₁ = {!mkRedTerm!}
  … | .(N-elim _ term Nₛ N-zero) | N-elim-zero-red .term Nₛ = {!!}
  … | .(N-elim _ N₀ Nₛ (N-succ M₁)) | N-elim-succ-red N₀ Nₛ M₁ = {!!}
  … | .(⇒-intr _ _ _) | ⇒-intr-red r = {!!}
  … | .(⇒-elim _ _ _ M₁) | ⇒-elim-N-red M₁ r = {!!}
  … | .(⇒-elim _ _ N _) | ⇒-elim-M-red N r = {!!}
  … | .(N-succ _) | N-succ-red r = {!!}

  unextextRedTerm : ∀ {Γ Γ'} → (α : Γ ≤ Γ') → (M : Term Γ) → (rtM : RedTerm M) → unextendRedTerm α M (extendRedTerm α M rtM) ≡ rtM
  unextextRedTerm = {!!}

  extunextRedTerm : ∀ {Γ Γ' M} → (α : Γ ≤ Γ') → (rtextM : RedTerm (extendTerm α M)) → extendRedTerm α M (unextendRedTerm α M rtextM) ≡ rtextM
  extunextRedTerm = {!!}

  extunextRedTermTerm : ∀ {Γ Γ'} → (M : Term Γ) → (α : Γ ≤ Γ') → (rtextM : RedTerm (extendTerm α M)) → RedTerm.term (extendRedTerm α M (unextendRedTerm α M rtextM)) ≡ RedTerm.term rtextM
  extunextRedTermTerm = {!!}

  unextextRedTermTerm : ∀ {Γ Γ'} {M : Term Γ} → (α : Γ ≤ Γ') → (rtM : RedTerm M) → RedTerm.term (unextendRedTerm α M (extendRedTerm α M rtM)) ≡ RedTerm.term rtM
  unextextRedTermTerm = {!!}

  extendSN : ∀ {Γ Γ' M} → (α : Γ ≤ Γ') → SN M → SN (extendTerm α M)
  extendSN {Γ} {Γ'} {M} α (mkSN sM) = mkSN lem
    where
      lem : (extM' : Term Γ') → (extr : Red (extendTerm α M) extM') → SN extM'
      lem extM' extr = transport SN (extunextRedTermTerm M α rtextM) (extendSN α (sM M' r'))
        where
          extM : Term Γ'
          extM = extendTerm α M

          rtextM : RedTerm extM
          rtextM = mkRedTerm extM' extr

          rtM : RedTerm M
          rtM = unextendRedTerm α M rtextM

          M' : Term Γ
          M' = RedTerm.term rtM

          r' : Red M M'
          r' = RedTerm.red rtM

  unextendSN : ∀ {Γ Γ' M} → (α : Γ ≤ Γ') → SN (extendTerm α M) → SN M
  unextendSN α (mkSN sM*) = mkSN (\M' r → unextendSN α (sM* (extendTerm α M') (extendRed α r)))

  extendNeutral : ∀ {Γ Γ' M} → (α : Γ ≤ Γ') → Neutral M → Neutral (extendTerm α M)
  extendNeutral α n-var = n-var
  extendNeutral α n-⇒-elim = n-⇒-elim

  mutual
    TypeVal'' : (Γ : Context) → (τ : Type) → (M : Term Γ) → Set
    TypeVal'' Γ (ρ ⇒ τ) M = (Γ' : Context) → (α : Γ ≤ Γ') → (U : Term Γ') → TypeVal' Γ' ρ U → TypeVal' Γ' τ (⇒-elim ρ τ U (extendTerm α M))
    TypeVal'' Γ Nat M = SN M

    -- TypeVal' : (Γ : Context) → (τ : Type) → (M : Term Γ) → Set 
    -- TypeVal' Γ τ M = SN M × TypeVal'' Γ τ M
    TypeVal' : (Γ : Context) → (τ : Type) → (M : Term Γ) → Set 
    TypeVal' Γ τ M = TypeVal'' Γ τ M
  
  cr2 : ∀ {Γ} → (τ : Type) → (M M' : Term Γ) → Red M M' → TypeVal' Γ τ M → TypeVal' Γ τ M'
  cr2 (ρ ⇒ τ) M M' r vM = \Γ' α N vN → cr2 τ _ _ (⇒-elim-M-red N (extendRed α r)) (vM Γ' α N vN)
  cr2 Nat M M' r (mkSN sM) = sM M' r
  {-
  cr2 : ∀ {Γ} → (τ : Type) → (M M' : Term Γ) → Red M M' → TypeVal' Γ τ M → TypeVal' Γ τ M'
  cr2 (ρ ⇒ τ) M M' r (mkSN sM , vM) = sM M' r , \Γ' α N vN → cr2 τ _ _ (⇒-elim-M-red N (extendRed α r)) (vM Γ' α N vN)
  cr2 Nat M M' r (mkSN sM , n) = sM M' r , n
  -}
  
  mutual
    cr3 : ∀ {Γ} → (τ : Type) → (M : Term Γ) → Neutral M → ((M' : Term Γ) → Red M M' → TypeVal' Γ τ M') → TypeVal' Γ τ M
    cr3 {Γ} (ρ ⇒ τ) M nM vrM = \Γ' α U vU → lem Γ' α U vU (cr1 ρ U vU)
      where
        lem : (Γ' : Context) → (α : Γ ≤ Γ') → (U : Term Γ') → TypeVal' Γ' ρ U → SN U → TypeVal' Γ' τ (⇒-elim ρ τ U (extendTerm α M))
        lem Γ' α U vU (mkSN sU) with extendTerm α M | extendNeutral α nM
        ... | M* | nM* = cr3 τ (⇒-elim ρ τ U M*) n-⇒-elim \K → \
          { (⇒-elim-N-red {N' = U'} M r) → {!lem Γ' α U' (cr2 ρ U U' r vU) (sU U' r)!}
          ; (⇒-elim-M-red {M' = M*'} N r) → {!vrM!}
          }
    cr3 Nat M nM vrM = mkSN (\M' r → vrM M' r)
  
    Vvar : ∀ Γ τ i → TypeVal' Γ τ (var i)
    Vvar Γ τ i = cr3 _ _ n-var (\M ())
    
    cr1 : ∀ {Γ} → (τ : Type) → (M : Term Γ) → TypeVal' Γ τ M → SN M
    cr1 {Γ} (ρ ⇒ τ) M vM = unextendSN (pass ρ idExt) (lem ρ τ $0 (extendTerm (pass ρ idExt) M) (cr1 τ M0 vM0))
      where
        $0 : Term (ρ ∷ Γ)
        $0 = var here

        M0 : Term (ρ ∷ Γ)
        M0 = ⇒-elim ρ τ $0 (extendTerm (pass ρ idExt) M)

        vM0 : TypeVal' (ρ ∷ Γ) τ M0
        vM0 = vM (ρ ∷ Γ) (pass ρ idExt) $0 (Vvar (ρ ∷ Γ) ρ here)

        lem : ∀ {Γ} ρ τ → (N M : Term Γ) → SN (⇒-elim ρ τ N M) → SN M
        lem ρ τ N M (mkSN s) = mkSN \M' r → lem ρ τ N M' (s (⇒-elim ρ τ N M') (⇒-elim-M-red N r))
    cr1 Nat M sM = sM
  

  abs-lem-lem : (Γ : Context) → (ρ τ : Type)
              → (M : Term (ρ ∷ Γ))
              → ((Γ' : Context) → (α : Γ ≤ Γ') → (U : Term Γ') → (vU : TypeVal' Γ' ρ U) → TypeVal' Γ' τ (bind (set ρ U (Ext⇛TermK α)) M))
              → SN M
              → (Γ' : Context) → (α : Γ ≤ Γ') → (N : Term Γ') → (vN : TypeVal' Γ' ρ N) → SN N
              → (K : Term Γ') → Red (⇒-elim ρ τ N (⇒-intr ρ τ (bind (Ext⇛TermK (match ρ α)) M))) K
              → TypeVal' Γ' τ K
  abs-lem-lem Γ ρ τ M vsM sM Γ' α N vN sN _ (⇒-elim-red _ _) = transport (\z → TypeVal' Γ' τ z) (elem1 M) (vsM Γ' α N vN)
    where
      elem1 : EqTermF (TermK⇛TermF (set ρ N (Ext⇛TermK α))) (composeTermF (TermK⇛TermF (set ρ N idTermK)) (Ext⇛TermF (match ρ α)))
      elem1 = {!!}
  abs-lem-lem Γ ρ τ M vsM sM Γ' α N vN (mkSN sN) .(⇒-elim ρ τ N' (⇒-intr ρ τ _)) (⇒-elim-N-red {N' = N'} _ r)
    = cr3 τ _ n-⇒-elim (\K' r' → abs-lem-lem Γ ρ τ M vsM sM Γ' α N' vN' (sN N' r) K' r')
    where
      vN' : TypeVal' Γ' ρ N'
      vN' = cr2 ρ N N' r vN
  abs-lem-lem Γ ρ τ M vsM (mkSN sM) Γ' α N vN sN .(⇒-elim ρ τ N (⇒-intr ρ τ _)) (⇒-elim-M-red _ (⇒-intr-red {M' = extM'} extr))
    = cr3 τ _ n-⇒-elim lem
    where
      lem : (K' : Term Γ') → (extr' : Red (⇒-elim ρ τ N (⇒-intr ρ τ extM')) K') → TypeVal' Γ' τ K'
      lem K' extr' = abs-lem-lem Γ ρ τ M' vsM' (sM M' r) Γ' α N vN sN K' r'
        where
          unext : RedTerm M
          unext = unextendRedTerm _ M (mkRedTerm extM' extr)

          M' : Term (ρ ∷ Γ)
          M' = RedTerm.term unext

          r : Red M M'
          r = RedTerm.red unext

          vsM' :(Γ' : Context) → (α : Γ ≤ Γ') → (U : Term Γ') → (vU : TypeVal' Γ' ρ U) → TypeVal' Γ' τ (bind (set ρ U (Ext⇛TermK α)) M')
          vsM' Γ' α U vU = cr2 τ (bind (set ρ U (Ext⇛TermK α)) M) (bind (set ρ U (Ext⇛TermK α)) M') (bindRed _ r) (vsM Γ' α U vU)

          r' : Red (⇒-elim ρ τ N (⇒-intr ρ τ (bind (Ext⇛TermK (match ρ α)) M'))) K'
          r' = {!extr'!}

      
  abs-lem : (Γ : Context) → (ρ τ : Type)
          → (M : Term (ρ ∷ Γ))
          → TypeVal' (ρ ∷ Γ) τ M
          → ((Γ' : Context) → (α : Γ ≤ Γ') → (U : Term Γ') → (vU : TypeVal' Γ' ρ U) → TypeVal' Γ' τ (bind (set ρ U (Ext⇛TermK α)) M))
          → (Γ' : Context) → (α : Γ ≤ Γ') → (N : Term Γ') → (vN : TypeVal' Γ' ρ N) → TypeVal' Γ' τ (⇒-elim ρ τ N (⇒-intr ρ τ (bind (Ext⇛TermK (match ρ α)) M)))
  abs-lem Γ ρ τ M vM vsM Γ' α N vN = cr3 τ _ n-⇒-elim \K r → abs-lem-lem Γ ρ τ M vsM sM Γ' α N vN sN K r 
    where
      sM : SN M
      sM = cr1 τ M vM
  
      sN : SN N
      sN = cr1 ρ N vN

  ContextVal' : (Δ Γ : Context) → (γ : TermK Γ Δ) → Set
  ContextVal' Δ Γ γ = (i : Elem Γ) → (τ : Type) → Has Γ i τ → TypeVal' Δ τ (γ i)

  extendTypeVal : ∀ {Γ Γ' τ M} → (α : Γ ≤ Γ') → TypeVal' Γ τ M → TypeVal' Γ' τ (extendTerm α M)
  extendTypeVal {τ = ρ ⇒ τ} {M = M} α vM = {!\Δ β U vU → ? , transport (\z → TypeVal'' Δ τ (⇒-elim ρ τ U z)) (elem1 β α M) (vM Δ (composeExt β α) U vU)!}
    where
      elem1 : ∀ {Γ Δ Ω} → (β : Δ ≤ Ω) → (α : Γ ≤ Δ) → EqTermF (Ext⇛TermF (composeExt β α)) (composeTermF (Ext⇛TermF β) (Ext⇛TermF α))
      elem1 = {!!}
  extendTypeVal {τ = Nat} α sM = extendSN α sM

  extendContextVal : ∀ {Γ Δ Δ' γ} → (α : Δ ≤ Δ') → ContextVal' Δ Γ γ → ContextVal' Δ' Γ (extendTermK α γ)
  extendContextVal α vγ i τ h = extendTypeVal α (vγ i τ h)

  skipContextVal : ∀ {Γ Δ} → (ρ : Type) → (γ : TermK Γ Δ) → ContextVal' Δ Γ γ → ContextVal' (ρ ∷ Δ) (ρ ∷ Γ) (skip ρ γ)
  skipContextVal ρ γ vγ here τ h = Vvar _ _ here
  skipContextVal ρ γ vγ (there i) τ (there h) = extendTypeVal (pass ρ idExt) (vγ i τ h)

  addContextVal : ∀ {Γ Δ} → (ρ : Type) → (U : Term Δ) → (vU : TypeVal' Δ ρ U) → {γ : TermK Γ Δ} → ContextVal' Δ Γ γ → ContextVal' Δ (ρ ∷ Γ) (set ρ U γ)
  addContextVal ρ U vU vγ here .ρ here = vU
  addContextVal ρ U vU vγ (there i) τ (there h) = vγ i τ h

  idContextVal : ∀ {Γ} → ContextVal' Γ Γ idTermK
  idContextVal i τ h = Vvar _ _ i

  TermVal' : ∀ {Γ τ M} → Valid Γ τ M → {Δ : Context} → (γ : TermK Γ Δ) → ContextVal' Δ Γ γ → TypeVal' Δ τ (bind γ M)
  TermVal' (#var i τ h) γ vγ = vγ i τ h
  TermVal' (#⇒-intr ρ τ M #M) {Δ} γ vγ = \Δ' α U vU → transport (\z → TypeVal' Δ' τ (⇒-elim ρ τ U z)) {!!} (abs-lem Δ ρ τ (bind (skip ρ γ) M) vM (\Δ'' β U' vU' → transport (\z → TypeVal' Δ'' τ z) {!!} (vsM Δ'' β U' vU')) Δ' α U vU)
    where
      vM : TypeVal' (ρ ∷ Δ) τ (bind (skip ρ γ) M)
      vM = TermVal' #M _ (skipContextVal ρ γ vγ)

      vsM : (Δ' : Context) → (α : Δ ≤ Δ') → (U : Term Δ') → TypeVal' Δ' ρ U → TypeVal' Δ' τ (bind (set ρ U (composeTermK (Ext⇛TermK α) γ)) M)
      vsM Δ' α U vU = TermVal' #M _ (addContextVal ρ U vU (extendContextVal α vγ))
  TermVal' (#⇒-elim ρ τ N #N M #M) {Δ} γ vγ = v[γ]M[γ]N
    where
      v[γ]M : TypeVal' Δ (ρ ⇒ τ) (bind γ M)
      v[γ]M = TermVal' #M γ vγ

      v[γ]N : TypeVal' Δ ρ (bind γ N)
      v[γ]N = TermVal' #N γ vγ

      v[idE][γ]M[γ]N : TypeVal' Δ τ (⇒-elim ρ τ (bind γ N) (bind (Ext⇛TermK idExt) (bind γ M)))
      v[idE][γ]M[γ]N = v[γ]M Δ idExt (bind γ N) v[γ]N

      elem1 : EqTermF (Ext⇛TermF idExt) idTermF
      elem1 = {!!}

      v[γ]M[γ]N : TypeVal' Δ τ (bind γ (⇒-elim ρ τ N M))
      v[γ]M[γ]N = transport (\z → TypeVal' Δ τ (⇒-elim _ _ _ z)) (elem1 (bind γ M)) v[idE][γ]M[γ]N
  TermVal' #N-zero γ vγ = sn-zero
  TermVal' (#N-succ M #M) γ vγ = sn-succ (bind γ M) (TermVal' #M γ vγ)
  TermVal' (#N-elim ρ N₀ #N₀ Nₛ #Nₛ M #M) γ vγ = {!TermVal' Γ #M γ vγ!}

sn : ∀ {Γ τ M} → Valid Γ τ M → SN M
sn {Γ} {τ} {M} #M = cr1 τ M vM
  where
    v[id]M : TypeVal' Γ τ (bind idTermK M)
    v[id]M = TermVal' #M idTermK idContextVal

    elem1 : EqTermF (TermK⇛TermF idTermK) idTermF
    elem1 M = {!!}

    vM : TypeVal' Γ τ M
    vM = transport (\z → TypeVal' _ _ z) (elem1 M) v[id]M
