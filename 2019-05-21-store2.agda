-- programming with ram
module _ where

-- lib
module _ where
  -- function
  module _ where
    _€_ : {A B : Set} → A → (A → B) → B
    x € f = f x

  -- finite (co)product
  module _ where
    data ⊥ : Set where

    record ⊤ : Set where
      constructor tt

    record _×_ (A B : Set) : Set where
      constructor _&_
      field
        fst : A
        snd : B
    open _×_ public

  -- bool
  module _ where
    data Bool : Set where
      false true : Bool
    {-# BUILTIN BOOL Bool #-}
    {-# BUILTIN TRUE true #-}
    {-# BUILTIN FALSE false #-}

    and : Bool → Bool → Bool
    and false _ = false
    and true y = y

  -- natural
  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

    eqℕ : ℕ → ℕ → Bool
    eqℕ zero zero = true
    eqℕ zero (succ m) = false
    eqℕ (succ n) zero = false
    eqℕ (succ n) (succ m) = eqℕ n m

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

  -- string
  module _ where
    postulate String : Set
    {-# BUILTIN STRING String #-}
    primitive primStringEquality : String → String → Bool

    eqString : String → String → Bool
    eqString = primStringEquality

module _ where
  Var : Set
  Var = String × ℕ

  eqVar : Var → Var → Bool
  eqVar (v & i) (v' & i') = and (primStringEquality v v') (eqℕ i i') 

  data Val : Set where
    number : ℕ → Val
    bool : Bool → Val
    undefined : Val

  -- memory
  module _ where
    Mem : Set
    Mem = List (Var × Val)

    get : Mem → Var → Maybe Val
    get ε v = nothing
    get ((v' & e) , m) v = eqVar v v' € \{ true → just e ; false → get m v }

    set : Mem → Var → Val → Mem
    set m v e = (v & e) , m 

  module _ where
    data %Program (L : Set) (A : Set) : Set where
      %return : A → %Program L A
      %read : Var → (Val → L) → %Program L A
      %write : Var → Val → L → %Program L A
      %fail : %Program L A

    record Program (A : Set) : Set where
      coinductive
      constructor #
      field % : %Program (Program A) A
    open Program public

    _>>=_ : {A B : Set} → Program A → (A → Program B) → Program B
    % (p >>= f) with % p
    … | %return a = % (f a)
    … | %read v p' = %read v \e → p' e >>= f
    … | %write v e p' = %write v e (p' >>= f)
    … | %fail = %fail

    return : {A : Set} → A → Program A
    % (return a) = %return a

    read : Var → Program Val
    % (read v) = %read v \e → return e

    write : Var → Val → Program ⊤
    % (write v e) = %write v e (return tt)

    fail : {A : Set} → Program A
    % fail = %fail

  module _ where
    readNumber : Var → Program ℕ
    readNumber v = read v >>= \{ (number a) → return a ; _ → fail }

    readBool : Var → Program Bool
    readBool v = read v >>= \{ (bool a) → return a ; _ → fail }

module _ where
  merge : Program ⊤
  merge = {!!}
