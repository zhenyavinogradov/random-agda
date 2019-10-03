module _ where

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

  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (succ n)
    succ : {n : ℕ} → Fin n → Fin (succ n)

  data Vector (A : Set) : ℕ → Set where
    ε : Vector A zero
    _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

  data AllV {A : Set} (P : A → Set) : {n : ℕ} → Vector A n → Set where
    ε : AllV P ε
    _∷_ : {n : ℕ} {a : A} {as : Vector A n} → P a → AllV P as → AllV P (a ∷ as)

  data _≡_ {A : Set} (a : A) : A → Set where
    refl : a ≡ a

  transport : {A : Set} → (P : A → Set) → {a a' : A} → a ≡ a' → P a → P a'
  transport P refl Pa = Pa

data Type : Set where
  -- π σ : List Type → Type
  _⇒_ : Type → Type → Type
  Nat : Type

postulate String : Set
{-# BUILTIN STRING String #-}

data Var : Set where
  $ : ℕ → String → Var

Abs : Set → Set
Abs T = Var × T

data Term : Set where
  var : (τ : Type) → (x : Var) → Term
  --llet : (ρ τ : Type) → (x : Var) → Term{-ρ-} → Term{-x:ρ⊢τ-} → Term{-τ-}

{-
  π-intr : (n : ℕ) → (τs : Vector Type n) → (Ms : Vector Term{-τᵢ-} n) → Term{-π τs-}
  π-elim : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-π τs-} → Term{-τᵢ-}

  σ-intr : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-τᵢ-} → Term{-σ τs-}
  σ-elim : (n : ℕ) → (τs : Vector Type n) → (ρ : Type) → (Ms : Vector (Abs Term{-τᵢ⊢ρ-}) n) → Term{-σ τs-} → Term{-ρ-}
  -}

  ⇒-intr : (ρ τ : Type) → (x : Var) → Term{-x:ρ⊢τ-} → Term{-ρ⇒τ-}
  ⇒-elim : (ρ τ : Type) → Term{-ρ-} → Term{-ρ⇒τ-} → Term{-τ-}

  N-elim : (ρ : Type) → Term{-ρ-} → (x : Var) → Term{-x:ρ⊢ρ-} → Term{-ℕ-} → Term{-ρ-}
  N-zero : Term{-ℕ-}
  N-succ : Term{-ℕ-} → Term{-ℕ-}

  M-nothing : (τ : Type) → Term{-Maybe τ-}
  M-just : (τ : Type) → Term{-τ-} → Term{-Maybe τ-}
  M-elim : (τ ρ : Type) → Term{-ρ-} → (x : Var) → Term{-x:τ⊢ρ-} → Term{-Maybe τ-} → Term{-ρ-}

  S-intr : (τ ρ : Type) → (x : Var) → Term{-x:ρ⊢τ-} → Term{-x:ρ⊢ρ-} → Term{-ρ-} → Term{-Stream τ-}
  S-head : (τ : Type) → Term{-Stream τ-} → Term{-τ-}
  S-tail : (τ : Type) → Term{-Stream τ-} → Term{-Stream τ-}

  CoN-intr : (ρ : Type) → (x : Var) → Term{-x:ρ⊢ρ-} → Term{-ρ-} → Term{-CoN-}
  CoN-elim : Term{-CoN-} → Term{-Maybe CoN-}

Context : Set
Context = List (Var × Type)

{-
data Has : Context → Var → Type → Set where
  here : ∀ {Γ x τ} → Has ((x , τ) ∷ Γ) x τ
  there : ∀ {Γ x τ p} → Has Γ x τ → Has (p ∷ Γ) x τ
  -}
Has : Context → Var → Type → Set
Has Γ x τ = {!!}

data Valid : Context → Type → Term → Set where
  #var : ∀ {Γ} → (x : Var) → (τ : Type) → (h : Has Γ x τ) → Valid Γ τ (var τ x)
  -- #llet : ∀ {Γ} → (ρ τ : Type) → (x : Var) → (N : Term{-ρ-}) → Valid Γ ρ N → (M : Term{-x:ρ⊢τ-}) → Valid ((x , ρ) ∷ Γ) τ M → Valid Γ τ (llet ρ τ x N M)

{-
  #π-intr : ∀ {Γ} → (n : ℕ) → (τs : Vector Type n) → (Ms : Vector Term{-τᵢ-} n) → AllV (Valid Γ {!!}
  #π-elim : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-π τs-} → Term{-τᵢ-} → {!!}

  #σ-intr : (n : ℕ) → (τs : Vector Type n) → (i : Fin n) → Term{-τᵢ-} → Term{-σ τs-} → {!!}
  #σ-elim : (n : ℕ) → (τs : Vector Type n) → (ρ : Type) → (Ms : Vector (Abs Term{-τᵢ⊢ρ-}) n) → Term{-σ τs-} → Term{-ρ-} → {!!}
  -}

  #⇒-intr : ∀ {Γ} → (ρ τ : Type) → (x : Var) → (M : Term{-x:ρ⊢τ-}) → Valid ((x , ρ) ∷ Γ) τ M → Valid Γ (ρ ⇒ τ) (⇒-intr ρ τ x M)
  #⇒-elim : ∀ {Γ} → (ρ τ : Type)
          → (N : Term{-ρ-}) → (#N : Valid Γ ρ N)
          → (M : Term{-ρ⇒τ-}) → (#M : Valid Γ (ρ ⇒ τ) M)
          → Valid Γ τ (⇒-elim ρ τ N M)

  #N-zero : ∀ {Γ} → Valid Γ Nat N-zero
  #N-succ : ∀ {Γ} → (M : Term{-ℕ-}) → Valid Γ Nat M → Valid Γ Nat (N-succ M)
  #N-elim : ∀ {Γ} → (ρ : Type)
         → (N₀ : Term{-ρ-}) → Valid Γ ρ N₀
         → (x : Var) → (Nₛ : Term{-x:ρ⊢ρ-}) → Valid ((x , ρ) ∷ Γ) ρ Nₛ
         → (M : Term{-ℕ-}) → Valid Γ Nat M
         → Valid Γ ρ (N-elim ρ N₀ x Nₛ M)

CSubst : Context → Set
CSubst ε = ⊤
CSubst ((_ , ρ) ∷ Γ) = Term × CSubst Γ

{-
record Subst : Set where
  constructor mkSubst
  field
    sskip : ℕ
    sterms : List Term
open Subst public

incSubst : Subst → Subst
sskip (incSubst s) = succ (sskip s)
sterms (incSubst s) = sterms s
-}
data Subst : Set where
  empty : Subst{-Γ⇒Γ-}
  set : (x : Var) → Term{-Δ⊢τ-} → Subst{-Γ⇒Δ-} → Subst{-x:τ,Γ⇒Δ-}
  skip : (x : Var) → Subst{-Γ⇒Δ-} → Subst{-x:ρ,Γ⇒x:ρ,Δ-}

_~_ : Subst → Subst → Set
_~_ = {!!}

apply : Subst{-Δ⇒Ω-} → Subst{-Γ⇒Δ-} → Subst{-Γ⇒Ω-}
apply = {!!}

subvar : Subst → Type → Var → Term
subvar = {!!}
{-
subvar (mkSubst _ ε) τ v@($ zero _) = var τ v
subvar (mkSubst zero (U ∷ Us)) τ ($ zero _) = U
subvar (mkSubst (succ s) (U ∷ Us)) τ v@($ zero _) = var τ v
subvar (mkSubst (succ s) (U ∷ Us)) τ v@($ (succ s') _) = var τ v
subvar (mkSubst s ts) τ ($ (succ x) x₁) = {!!}
-}

-- asubst : {Γ : Context} → CSubst Γ → Term → Term
asubst : Subst{-Γ⇒Δ-} → Term{-Γ,Ω⊢τ-} → Term{-Δ,Ω⊢τ-}
asubst γ (var τ x) = subvar γ τ x
-- asubst γ (llet ρ τ x M M₁) = {!!}
asubst γ (⇒-intr ρ τ x M) = ⇒-intr ρ τ x (asubst (skip x γ) M)
asubst γ (⇒-elim ρ τ N M) = ⇒-elim ρ τ (asubst γ N) (asubst γ M)
asubst γ (N-elim ρ N₀ x Nₛ M) = N-elim ρ (asubst γ N₀) x (asubst (skip x γ) Nₛ) (asubst γ M) 
asubst γ N-zero = N-zero
asubst γ (N-succ M) = N-succ (asubst γ M)
asubst γ _ = {!!}

{-
  asubst γ₁{Δ⇒Ω} (asubst γ₂{Γ⇒Δ} M{Γ⊢τ}) = asubst (apply γ₁ γ₂){Γ⇒Ω} (asubst γ₁{Δ⇒Ω} M{Γ⊢τ}){Δ}
-}

eqSubst : {γ γ' : Subst} → γ ~ γ' → (M : Term) → asubst γ M ≡ asubst γ' M
eqSubst = {!!}

subst : (x : Var) → Term{-Γ⊢ρ-} → Term{-x:ρ,Γ⊢τ-} → Term{-Γ⊢τ-}
subst x N M = asubst (set x N empty) M

data Red : Term → Term → Set where
  ⇒-elim-red : ∀ {ρ τ} N x M → Red (⇒-elim ρ τ N (⇒-intr ρ τ x M)) (subst x N M)
  N-elim-zero-red : ∀ {ρ} N₀ x Nₛ → Red (N-elim ρ N₀ x Nₛ N-zero) N₀
  N-elim-succ-red : ∀ {ρ} N₀ x Nₛ M → Red (N-elim ρ N₀ x Nₛ (N-succ M)) (subst x (N-elim ρ N₀ x Nₛ M) Nₛ)

  ⇒-intr-red : ∀ {ρ τ x M M'} → Red M M' → Red (⇒-intr ρ τ x M) (⇒-intr ρ τ x M')
  ⇒-elim-N-red : ∀ {ρ τ N N'} → (M : Term) → Red N N' → Red (⇒-elim ρ τ N M) (⇒-elim ρ τ N' M)
  ⇒-elim-M-red : ∀ {ρ τ M M'} → (N : Term) → Red M M' → Red (⇒-elim ρ τ N M) (⇒-elim ρ τ N M')
  N-succ-red : ∀ {M M'} → Red M M' → Red (N-succ M) (N-succ M')

-- lem-subst-red : (x : Var) → (U M M' : Term) → Red M M' → Red (subst x U M) (subst x U M')
lem-subst-red : (γ : Subst) → {M M' : Term} → Red M M' → Red (asubst γ M) (asubst γ M')
lem-subst-red γ (⇒-elim-red N y M) = {!⇒-elim-red (asubst γ N) y (asubst (skip y γ) M)!}
lem-subst-red γ (N-elim-zero-red N₀ x Nₛ) = N-elim-zero-red (asubst γ N₀) x (asubst (skip x γ) Nₛ)
lem-subst-red γ (N-elim-succ-red N₀ x Nₛ M) = {!N-elim-succ-red (asubst γ N₀) x (asubst (skip x γ) Nₛ) (asubst γ M)!}
lem-subst-red γ (⇒-intr-red {x = x} r) = ⇒-intr-red (lem-subst-red (skip x γ) r)
lem-subst-red γ (⇒-elim-N-red M r) = ⇒-elim-N-red (asubst γ M) (lem-subst-red γ r)
lem-subst-red γ (⇒-elim-M-red N r) = ⇒-elim-M-red (asubst γ N) (lem-subst-red γ r)
lem-subst-red γ (N-succ-red r) = N-succ-red (lem-subst-red γ r)

-- lem-subst-asubst : {Γ : Context} → ∀ U x M → (γ : CSubst Γ) → asubst {Γ = {!!}} (U , γ) M ≡ subst x U (asubst γ M)
lem-subst-asubst : ∀ U x M → (γ : Subst) → asubst {!!} M ≡ subst x U (asubst γ M)
lem-subst-asubst = {!!}

lem-subst-id : ∀ x τ M → subst x (var τ x) M ≡ M
lem-subst-id = {!!}

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

data SN (M : Term) : Set where
  mkSN : ((M' : Term) → Red M M' → SN M') → SN M

TypeVal' : Type → Term → Set
TypeVal' (ρ ⇒ τ) M = (U : Term) → TypeVal' ρ U → TypeVal' τ (⇒-elim ρ τ U M)
TypeVal' Nat M = SN M

-- ContextVal' : (Γ : Context) → CSubst Γ → Set
-- ContextVal' ε tt = ⊤
-- ContextVal' ((x , ρ) ∷ Γ) (Mx , MΓ) = TypeVal' ρ Mx  × ContextVal' Γ MΓ
ContextVal' : (Γ : Context) → Subst → Set
ContextVal' = {!!}

data TRCl {A : Set} (R : A → A → Set) : A → A → Set where
  ε : (a : A) → TRCl R a a
  _∷_ : {a b c : A} → R a b → TRCl R b c → TRCl R a c

Red* : Term → Term → Set
Red* = TRCl Red

cr2 : (τ : Type) → (M M' : Term) → Red M M' → TypeVal' τ M → TypeVal' τ M'
cr2 (ρ ⇒ τ) M M' r vM = \N vN → cr2 τ (⇒-elim ρ τ N M) (⇒-elim ρ τ N M') (⇒-elim-M-red N r) (vM N vN)
cr2 Nat M M' r (mkSN sM) = sM M' r

data Neutral : Term → Set where
  n-var : ∀ {τ x} → Neutral (var x τ)
  n-⇒-elim : ∀ {ρ τ N M} → Neutral (⇒-elim ρ τ N M)

mutual
  cr3 : (τ : Type) → (M : Term) → Neutral M → ((M' : Term) → Red M M' → TypeVal' τ M') → TypeVal' τ M
  cr3 (ρ ⇒ τ) M nM vrM = \U vU → lem ρ τ M nM vrM U vU (cr1 ρ U vU)
    where
      lem : ∀ ρ τ M → (nM : Neutral M) → (vrM : (M' : Term) → Red M M' → TypeVal' (ρ ⇒ τ) M') → (U : Term) → TypeVal' ρ U → SN U → TypeVal' τ (⇒-elim ρ τ U M)
      lem ρ τ M nM vrM U vU (mkSN sU) = cr3 τ (⇒-elim ρ τ U M) n-⇒-elim \K → \
        { (⇒-elim-N-red {N' = U'} M r) → lem ρ τ M nM vrM U' (cr2 ρ U U' r vU) (sU U' r)
        ; (⇒-elim-M-red {M' = M'} N r) → vrM M' r U vU
        }
  cr3 Nat M nM vrM = mkSN vrM
  
  cr1 : (τ : Type) → (M : Term) → TypeVal' τ M → SN M
  cr1 (ρ ⇒ τ) M vM = lem ρ τ $x M (cr1 τ (⇒-elim ρ τ $x M) (vM $x (cr3 ρ $x n-var (\M' ()))))
    where
      $x = var ρ ($ {!!} "x")

      lem : ∀ ρ τ N M → SN (⇒-elim ρ τ N M) → SN M
      lem ρ τ N M (mkSN s) = mkSN \M' r → lem ρ τ N M' (s (⇒-elim ρ τ N M') (⇒-elim-M-red N r))
  cr1 Nat M sM = sM

lem1 : (ρ τ : Type) → (x : Var) → (M : Term)
     → ((U : Term) → TypeVal' ρ U → TypeVal' τ (subst x U M))
     → SN M
     → (N : Term) → (TypeVal' ρ N) → SN N
     → (K : Term) → Red (⇒-elim ρ τ N (⇒-intr ρ τ x M)) K
     → TypeVal' τ K
lem1 ρ τ x M vsM sM N vN sN _ (⇒-elim-red _ _ _) = vsM N vN
lem1 ρ τ x M vsM sM N vN (mkSN sN) .(⇒-elim ρ τ N' (⇒-intr ρ τ x M)) (⇒-elim-N-red {N' = N'} _ r)
  = cr3 τ _ n-⇒-elim (\K' r' → lem1 ρ τ x M vsM sM N' (cr2 ρ N N' r vN) (sN N' r) K' r')
lem1 ρ τ x M vsM (mkSN sM) N vN sN .(⇒-elim ρ τ N (⇒-intr ρ τ x _)) (⇒-elim-M-red _ (⇒-intr-red {M' = M'} r))
  = cr3 τ _ n-⇒-elim (\K' r' → lem1 ρ τ x M' (\U vU → cr2 τ (subst x U M) (subst x U M') (lem-subst-red (set x U empty) r) (vsM U vU) ) (sM M' r) N vN sN K' r')

abs-lem : (ρ τ : Type)
        → (x : Var) → (M : Term{-x:ρ⊢τ-})
        → ((U : Term{-ρ-}) → (vU : TypeVal' ρ U) → TypeVal' τ (subst x U M))
        → (N : Term) → (vN : TypeVal' ρ N) → TypeVal' τ (⇒-elim ρ τ N (⇒-intr ρ τ x M))
        -- → TypeVal' (ρ ⇒ τ) (⇒-intr ρ τ x M)
abs-lem ρ τ x M vsM N vN = cr3 τ (⇒-elim ρ τ N (⇒-intr ρ τ x M)) n-⇒-elim \K r → lem1 ρ τ x M vsM (cr1 τ M (transport (\K → TypeVal' τ K) (lem-subst-id x ρ M) (vsM (var ρ x) (cr3 _ _ n-var (\M ()))))) N vN (cr1 ρ N vN) K r 

sn-zero : SN N-zero
sn-zero = mkSN \M' ()

sn-succ : (M : Term) → SN M → SN (N-succ M)
sn-succ M (mkSN sM) = mkSN (\succM' → \{ (N-succ-red {M' = M'} r) → sn-succ M' (sM M' r)})

-- TermVal' : {Γ : Context} → {τ : Type} → {M : Term} → Valid Γ τ M → (γ : CSubst Γ) → ContextVal' Γ γ → TypeVal' τ (asubst γ M)
TermVal' : (Γ : Context) → {τ : Type} → {M : Term} → Valid Γ τ M → (γ : Subst) → ContextVal' Γ γ → TypeVal' τ (asubst γ M)
TermVal' Γ (#var x τ h) γ vγ = {!!}
-- TermVal' (#llet ρ τ x N #N M #M) γ vγ = {!!}
TermVal' Γ (#⇒-intr ρ τ x M #M) γ vγ = \U vU → {!TermVal' ? #M (set x U empty) !} -- abs-lem ρ τ x (asubst γ M) \U vU → transport (\T → TypeVal' τ T) {!!} (TermVal' {!!} #M {!!} {!!})
TermVal' Γ (#⇒-elim ρ τ N #N M #M) γ vγ = TermVal' Γ #M γ vγ (asubst γ N) (TermVal' Γ #N γ vγ)
TermVal' Γ #N-zero γ vγ = sn-zero
TermVal' Γ (#N-succ M #M) γ vγ = sn-succ (asubst γ M) (TermVal' Γ #M γ vγ)
TermVal' Γ (#N-elim ρ N₀ #N₀ x Nₛ #Nₛ M #M) γ vγ = {!TermVal' #M!}
