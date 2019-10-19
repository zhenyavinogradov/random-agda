module _ where

module _ where
  _€_ : {A B : Set} → A → (A → B) → B
  x € f = f x

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  single : {A : Set} → A → List A
  single a = a ∷ ε

  data Elem {A : Set} : List A → Set where
    here : ∀ {x xs} → Elem (x ∷ xs)
    there : ∀ {x xs} → Elem xs → Elem (x ∷ xs)

  get : {A : Set} → {xs : List A} → Elem xs → A
  get {xs = x ∷ _} here = x
  get {xs = _ ∷ xs} (there i) = get i

{-
  infix 4 _≤_
  data _≤_ {A : Set} : List A → List A → Set where
    nil : ε ≤ ε
    drop : ∀ {xs ys} y → xs ≤ ys → xs ≤ y ∷ ys
    keep : ∀ {xs ys} x → xs ≤ ys → x ∷ xs ≤ x ∷ ys
    -}

data Type : Set where
  -- Bot : Type
  Nat : Type
  _⇒_ : Type → Type → Type

Context : Set
Context = List Type

infix 4 _≤_
_≤_ : Context → Context → Set
_≤_ Γ Δ = Elem Γ → Elem Δ

data Var : Context → Type → Set where
  -- Var [τ] τ
  $ : ∀ {Γ₀ τ} → single τ ≤ Γ₀ → Var Γ₀ τ

data Term : Context → Set where
  var : ∀ {Γ₀} → (τ : Type)
        → single τ ≤ Γ₀
        → Term Γ₀

  ⇒-intr : ∀ {Γ} → (ρ τ : Type)
         → {Γ_M : Context} → (M : Term Γ_M) → (Γ_M ≤ ρ ∷ Γ)
         → Term Γ
  ⇒-elim : ∀ {Γ} → (ρ τ : Type)
         → {Γ_N : Context} → (N : Term Γ_N) → (Γ_N ≤ Γ)
         → {Γ_M : Context} → (M : Term Γ_M) → (Γ_M ≤ Γ)
         → Term Γ

  N-zero : ∀ {Γ}
         → Term Γ
  N-succ : ∀ {Γ}
         → {Γ_M : Context} → (M : Term Γ_M) → Γ_M ≤ Γ
         → Term Γ
  N-elim : ∀ {Γ} → (ρ : Type)
         → {Γ_N₀ : Context} → (N₀ : Term Γ_N₀) → Γ_N₀ ≤ Γ
         → {Γ_Nₛ : Context} → (Nₛ : Term Γ_Nₛ) → Γ_Nₛ ≤ ρ ∷ Γ
         → {Γ_M : Context} → (M : Term Γ_M) → Γ_M ≤ Γ
         → Term Γ

module _ where
  TermF TermK : (Γ Δ : Context) → Set
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
  -- idExt {ε} = nil
  -- idExt {ρ ∷ Γ} = keep ρ (idExt {Γ})
  idExt i = i

{-
  idTermK : Identity TermK
  idTermK i = var (get i) {!!}
  -}

  idTermF : Identity TermF
  idTermF i = i

{-
  composeExt : Compose _≤_
  composeExt nil β = β
  composeExt (keep ρ α) (keep .ρ β) = keep ρ (composeExt α β)
  composeExt (keep ρ α) (drop .ρ β) = drop ρ (composeExt α β)
  composeExt (drop ρ α) β = drop ρ (composeExt α β)
  -}
  composeExt : Compose _≤_
  composeExt f g i = f (g i)

  composeTermF : Compose TermF
  composeTermF f g M = f (g M)

  keep : ∀ {Γ Δ} → (ρ : Type) → Γ ≤ Δ → (ρ ∷ Γ) ≤ (ρ ∷ Δ)
  keep ρ α here = here
  keep ρ α (there i) = there (α i)

  drop : ∀ {Γ Δ} → (ρ : Type) → Γ ≤ Δ → Γ ≤ (ρ ∷ Δ)
  drop ρ α i = there (α i)

  Ext⇛TermF : ∀ {Γ Δ} → Γ ≤ Δ → (Term Γ → Term Δ)
  Ext⇛TermF α (var τ τ≤Γ) = var τ (composeExt α τ≤Γ)
  Ext⇛TermF α (⇒-intr ρ τ M ΓM≤Γ) = ⇒-intr ρ τ (Ext⇛TermF (composeExt (keep ρ α) ΓM≤Γ) M) idExt
  Ext⇛TermF α (⇒-elim ρ τ N ΓN≤Γ M ΓM≤Γ) = ⇒-elim ρ τ (Ext⇛TermF (composeExt α ΓN≤Γ) N) idExt (Ext⇛TermF (composeExt α ΓM≤Γ) M) idExt
  Ext⇛TermF α (N-elim ρ N₀ ΓN₀≤Γ Nₛ ΓNₛ≤Γ M ΓM≤Γ) = N-elim ρ (Ext⇛TermF (composeExt α ΓN₀≤Γ) N₀) idExt (Ext⇛TermF (composeExt (keep ρ α) ΓNₛ≤Γ) Nₛ) idExt (Ext⇛TermF (composeExt α ΓM≤Γ) M) idExt
  Ext⇛TermF α N-zero = N-zero
  Ext⇛TermF α (N-succ M ΓM≤Γ) = N-succ (Ext⇛TermF (composeExt α ΓM≤Γ) M) idExt

{-
  ε≤ : (Γ : Context) → ε ≤ Γ
  ε≤ ε = nil
  ε≤ (x ∷ Γ) = drop x (ε≤ Γ)
  -}
  ε≤ : {Γ : Context} → ε ≤ Γ
  ε≤ ()

  skipTermK : {Γ Δ : Context} → (ρ : Type) → (Elem Γ → Term Δ) → (Elem (ρ ∷ Γ) → Term (ρ ∷ Δ))
  skipTermK ρ f  = \{ here → var ρ (keep ρ ε≤) ; (there i) → Ext⇛TermF (drop ρ idExt) (f i) }

  subvar : ∀ {Γ Δ} → (τ : Type) → ∀ {Γ' Δ'} → (Elem Γ' → Term Δ') → Γ ≤ Γ' → Δ' ≤ Δ → (single τ ≤ Γ → Term Δ)
  subvar τ f i = {!!}

  -- subst1 : Term Γ → Term (σ ∷ Γ) → Term Γ
  subst1 : ∀ {Γ} → (σ : Type)
         → {Γ_U : Context} → (U : Term Γ_U) → Γ_U ≤ Γ
         → {Γ_K : Context} → (K : Term Γ_K) → Γ_K ≤ σ ∷ Γ
         -- → {Γ₀ : Context} → Γ ≤ Γ₀ → Term Γ₀
         → Term Γ
  subst1 σ U ΓU≤Γ (var τ τ≤ΓU) ΓK≤σΓ =
    {!!}
  subst1 σ U ΓU≤Γ (⇒-intr ρ τ M ΓM≤ρΓ) ΓK≤σΓ =
    ⇒-intr ρ τ
    (subst1 σ U (drop ρ ΓU≤Γ) M {!\i → ΓM≤ρΓ i € \{here → there here ; (there j) → ΓK≤σΓ j € \{here → here ; (there k) → there (there k) } }!}) idExt
  subst1 σ U ΓU≤Γ (⇒-elim ρ τ N ΓN≤ΓU M ΓM≤ΓU) ΓK≤σΓ =
    ⇒-elim ρ τ
    (subst1 σ U ΓU≤Γ N (composeExt ΓK≤σΓ ΓN≤ΓU)) idExt
    (subst1 σ U ΓU≤Γ M (composeExt ΓK≤σΓ ΓM≤ΓU)) idExt
  subst1 σ U ΓU≤Γ (N-elim ρ N₀ ΓN₀≤ΓU Nₛ ΓNₛ≤ΓU M ΓM≤ΓU) ΓK≤σΓ =
    N-elim ρ
    (subst1 σ U ΓU≤Γ N₀ {!!}) idExt
    (subst1 σ U (drop ρ ΓU≤Γ) Nₛ {!!}) idExt
    (subst1 σ U ΓU≤Γ M {!!}) idExt
  subst1 σ U ΓU≤Γ N-zero ΓK≤σΓ =
    N-zero
  subst1 σ U ΓU≤Γ (N-succ M ΓM≤ΓU) ΓK≤σΓ =
    N-succ
    (subst1 σ U ΓU≤Γ M {!!}) idExt

  -- (Elem Γ → Term Δ) → (Term Γ → Term Δ)
  TermK⇛TermF : ∀ {Γ Δ} → ∀ {Γ' Δ'} → TermK Γ' Δ' → Γ ≤ Γ' → Δ' ≤ Δ → ({Γ_U : Context} → (U : Term Γ_U) → Γ_U ≤ Γ → Term Δ)
  TermK⇛TermF f Γ≤Γ' Δ'≤Δ (var τ τ≤ΓU) ΓU≤Γ =
    subvar τ f Γ≤Γ' Δ'≤Δ (composeExt ΓU≤Γ τ≤ΓU)
  TermK⇛TermF f Γ≤Γ' Δ'≤Δ (⇒-intr ρ τ M ΓM≤ρΓ) ΓU≤Γ =
    ⇒-intr ρ τ
    (TermK⇛TermF {!f!} {!!} {!!} M (composeExt (keep ρ ΓU≤Γ) ΓM≤ρΓ)) idExt
  TermK⇛TermF f Γ≤Γ' Δ'≤Δ (⇒-elim ρ τ N ΓN≤ΓU M ΓM≤ΓU) ΓU≤Γ =
    ⇒-elim ρ τ
    (TermK⇛TermF f {!!} {!!} N (composeExt ΓU≤Γ ΓN≤ΓU)) idExt
    (TermK⇛TermF f {!!} {!!} M (composeExt ΓU≤Γ ΓM≤ΓU)) idExt
  TermK⇛TermF f Γ≤Γ' Δ'≤Δ (N-elim ρ N₀ ΓN₀≤ΓU Nₛ ΓNₛ≤ΓU M ΓM≤ΓU) ΓU≤Γ =
    N-elim ρ
    (TermK⇛TermF f {!!} {!!} N₀ (composeExt ΓU≤Γ ΓN₀≤ΓU)) idExt
    (TermK⇛TermF (skipTermK ρ f) {!!} {!!} Nₛ (composeExt (keep ρ ΓU≤Γ) ΓNₛ≤ΓU)) idExt
    (TermK⇛TermF f {!!} {!!} M (composeExt ΓU≤Γ ΓM≤ΓU)) idExt
  TermK⇛TermF f Γ≤Γ' Δ'≤Δ N-zero ΓU≤Γ =
    N-zero
  TermK⇛TermF f Γ≤Γ' Δ'≤Δ (N-succ M ΓM≤ΓU) ΓU≤Γ =
    N-succ
    (TermK⇛TermF f {!!} {!!} M (composeExt ΓU≤Γ ΓM≤ΓU)) idExt

  {-
  subst : ∀ {Γ} → (ρ : Type) → single ρ ≤ Γ → Term Γ → Term Γ → Term Γ
  subst = {!!}
  -}

  
{-
  composeTermK : Compose TermK
  composeTermK γ₁ γ₂ i = (TermK⇛TermF γ₁) (γ₂ i)
  -}

{-
  Ext⇛TermK : _≤_ ⇛ TermK
  Ext⇛TermK α = ElemF⇛TermK (Ext⇛ElemF α)
  -}

{-
  Ext⇛TermF : _≤_ ⇛ TermF
  Ext⇛TermF α = TermK⇛TermF (Ext⇛TermK α)
  -}


{-
  set : ∀ {Γ Δ} → (ρ : Type) → (U : Term Δ) → (γ : TermK Γ Δ) → TermK (ρ ∷ Γ) Δ
  set ρ U γ = \{ here → U ; (there i) → γ i }

  skip : ∀ {Γ Δ} → (ρ : Type) → (γ : TermK Γ Δ) → TermK (ρ ∷ Γ) (ρ ∷ Δ)
  skip ρ γ = set ρ (var here) (composeTermK (Ext⇛TermK (drop ρ idExt)) γ)
  -}


{-
  bind : {Γ Δ : Context} → TermK Γ Δ → Term Γ → Term Δ
  bind = TermK⇛TermF

  -}
