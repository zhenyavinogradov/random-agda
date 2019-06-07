-- binary data
module _ where

module _ where
  -- (co)product
  module _ where
    record _×_ (A B : Set) : Set where
      field
       fst : A
       snd : B
    open _×_ public
 
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

    add : ℕ → ℕ → ℕ
    add zero m = m
    add (succ n) m = succ (add n m)

    mul : ℕ → ℕ → ℕ
    mul zero m = m
    mul (succ n) m = add n (mul n m)

    data _≤_ : ℕ → ℕ → Set where

  -- fin
  module _ where
    data Fin : ℕ → Set where
      zero : ∀ {k} → Fin (succ k)
      succ : ∀ {k} → Fin k → Fin (succ k)

    toℕ : ∀ {k} → Fin k → ℕ
    toℕ zero = zero
    toℕ (succ n) = succ (toℕ n)

    fromℕ : (k s : ℕ) → s ≤ k → Fin k
    fromℕ k s = {!!}

    subFin : (n : ℕ) → (m : Fin (succ n)) → ℕ
    subFin n zero = n
    subFin (succ n) (succ m) = subFin n m

    divMod : (n k : ℕ) → ℕ × Fin k
    divMod = {!!}

  -- maybe
  module _ where
    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just : A → Maybe A

  -- list
  module _ where
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

  -- vector
  module _ where
    data Vector (A : Set) : ℕ → Set where
      ε : Vector A zero
      _,_ : ∀ {n} → A → Vector A n → Vector A (succ n)

    toList : ∀ {A n} → Vector A n → List A
    toList ε = ε
    toList (a , as) = a , toList as


module _ where
  Byte : Set
  Byte = Vector Bool 8

  u1 : Bool → ℕ
  u1 false = 0
  u1 true = 1

  fromNary : (k : ℕ) → List (Fin k) → ℕ
  fromNary k ε = zero
  fromNary k (b , bs) = add (toℕ b) (mul k (fromNary k bs))

  toNary : (k : ℕ) → (s : ℕ) → List (Fin k)
  toNary k s = {!!}

  u8 : Byte → ℕ
  u8 = {!!}

  Parser : Set → Set
  Parser A = List Byte → Maybe (A × List Byte)
