module _ where

module _ where
  data _+_ {l} (A B : Set l) : Set l where
    inl : A → A + B
    inr : B → A + B

  record _×_ {l} (A B : Set l) : Set l where
    constructor _,_
    field
      fst : A
      snd : B

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,,_
    field
      first : A
      second : B first

  ∃ : {A : Set} → (B : A → Set) → Set
  ∃ = Σ _

data Fml (A : Set) : Set where
  var : (p : A) → Fml A
  _∧_ _∨_ _⇒_ : (ϕ : Fml A) → (ψ : Fml A) → Fml A
  ◽_ ◇_ : (ϕ : Fml A) → Fml A

Pred : Set → Set₁
Pred A = A → Set

infix 10 _⇔_
_⇔_ : Set → Set → Set₁
_⇔_ A B = A → B → Set

-- Val : {A W : Set} → (W → Pred (A + W)) → (W → Pred (Fml A))

Val : {A W : Set} → (A + W ⇔ W) → (Fml A ⇔ W)
Val V (var p) w = V (inl p) w
Val V (ϕ ∧ ψ) w = Val V ϕ w × Val V ψ w
Val V (ϕ ∨ ψ) w = Val V ϕ w + Val V ψ w
Val V (ϕ ⇒ ψ) w = Val V ϕ w → Val V ψ w
Val V (◽ ϕ) w = ∀ w' → V (inr w') w → Val V ϕ w'
Val V (◇ ϕ) w = ∃ \w' → V (inr w') w × Val V ϕ w'

IsLogic : {A : Set} → Pred (Fml A) → Set
IsLogic = {!!}
