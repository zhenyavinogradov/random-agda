module _ where

module _ where
  infixr 5 _,_
  infixr 15 _×_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

-- examples
module _ where
  data Bool : Set where
    false true : Bool
  
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}
  
  postulate String : Set
  {-# BUILTIN STRING String #-}
  
  record Device : Set where
    constructor mkDevice
    field
      block : Bool
      major : ℕ
      minor : ℕ
  
  exampleDevice : Device
  exampleDevice = mkDevice false 19 1
  
  record Benchmark (A : Set) : Set where
    constructor mkBenchmark
    field
      firstApp : A
      firstLog : String
      secondApp : A
      secondLog : String

-- lists
module _ where
  infixr 10 _∷_
  data List {l} (A : Set l) : Set l where
    ε : List A
    _∷_ : A → List A → List A
  
  data And : (As : List Set) → Set where
    ε : And ε
    _∷_ : ∀ {A As'} → A → And As' → And (A ∷ As')

  data All {l} {A : Set l} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  data All2 {l} {A B : Set l} (R : A → B → Set) : List A → List B → Set where
    ε : All2 R ε ε
    _∷_ : ∀ {a b as bs} → R a b → All2 R as bs → All2 R (a ∷ as) (b ∷ bs)

  All3 : ∀ {l} {A B C : Set l} (F : A → B → C → Set) → List A → List B → List C → Set
  All3 F as bs cs = {!!}

  maph : {As : List Set} {S : Set} → All (\A → (A → S)) As → And As → List S
  maph ε ε = ε
  maph (f ∷ fs) (a ∷ as) = f a ∷ maph fs as

  mapp : {As Bs : List Set} → All2 (\A B → (A → B)) As Bs → And As → And Bs
  mapp ε ε = ε
  mapp (f ∷ fs) (a ∷ as) = f a ∷ mapp fs as

  zip : {As Bs Cs : List Set} → All3 (\A B C → (A → B → C)) As Bs Cs → And As → And Bs → And Cs
  zip = {!!}

LispDevice : Set
LispDevice = And (Bool ∷ ℕ ∷ ℕ ∷ ε)

unDeviceLisp : Device → LispDevice
unDeviceLisp (mkDevice b x y) = b ∷ x ∷ y ∷ ε

LispBenchmark : Set → Set
LispBenchmark A = And (A ∷ String ∷ A ∷ String ∷ ε)

unBenchmarkLisp : {A : Set} → Benchmark A → LispBenchmark A
unBenchmarkLisp (mkBenchmark a b c d) = a ∷ b ∷ c ∷ d ∷ ε

showa' : ∀ {A As S} → List S × And (A ∷ As) → (A → S) → List S × And As
showa' (s , x ∷ xs) f = f x ∷ s , xs

depureMap : ∀ {A Bs} {T : Set} → A → (T → And Bs) → T → And (A ∷ Bs)
depureMap c f r = c ∷ f r

chop2 : ∀ {S A As B Bs} {T : Set} → S × And (A ∷ As) × And (B ∷ Bs) → (S → A → B → T) → T × And As × And Bs
chop2 (s , a ∷ as , b ∷ bs) f = f s a b , as , bs

_`andThen`_ : {A B : Set} → A → (A → B) → B
x `andThen` f = f x
