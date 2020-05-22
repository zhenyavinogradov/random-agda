

module Test where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  &succ : ∀ {Γ} → Term Γ #Nat → Term Γ #Nat
  &succ n = wrap (intr (intrNat (&inr n)))

  #zero : ∀ {Γ} → Term Γ #Nat
  #zero = wrap (intr (intrNat (&inl #unit)))
  
  #add : Term ε (#Nat ⇒ #Nat ⇒ #Nat)
  #add = #lambda (#lambda (&foldNat (var $1) (#lambda (&succ (var $0))) (var $0)))
  
  fromNat : ℕ → Term ε #Nat
  fromNat zero = #zero
  fromNat (succ n) = &succ (fromNat n)

  toNat : Value #Nat → ℕ
  toNat (construct (intrNat (construct (intrSum (here x))))) = zero
  toNat (construct (intrNat (construct (intrSum (there (here n)))))) = succ (toNat n)

  test : ℕ → ℕ → Term ε #Nat
  test n m = &apply (&apply #add (fromNat n)) (fromNat m)

  data Bool : Set where
    false true : Bool

  toBool : Value #Bool → Bool
  toBool (construct (intrSum (here _))) = false
  toBool (construct (intrSum (there (here _)))) = true

  record _↔_ (A B : Set) : Set where
    field
      to : A → B
      from : B → A

  IsDecider : Term ε ((#Nat ⇒ #Bool) ⇒ #Bool) → Set
  IsDecider all =
      (f : Term ε (#Nat ⇒ #Bool))
    → (toBool (evaluate (&apply all f)) ≡ true) ↔ ((n : Term ε #Nat) → toBool (evaluate (&apply f n)) ≡ true)
  
  --_ : {!!}
  --_ = {!toNat (result (run' (compile (test 5 9))))!}
