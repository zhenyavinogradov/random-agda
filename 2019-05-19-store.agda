-- programming with random access memory
module _ where

module _ where
  -- function
  module _ where
    _€_ : {A B : Set} → A → (A → B) → B
    x € f = f x

  -- equality
  module _ where
    data _≡_ {A : Set} (a : A) : A → Set where
      refl : a ≡ a

  -- finite (co)product
  module _ where
    data ⊥ : Set where

    record ⊤ : Set where
      constructor tt

    infixr 10 _+_
    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    infixr 15 _×_
    record _×_ (A B : Set) : Set where
      constructor _,,_
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

  -- string
  module _ where
    postulate
      String : Set
    {-# BUILTIN STRING String #-}

    primitive
      primStringEquality : String → String → Bool

  -- maybe
  module _ where
    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just : A → Maybe A

    maybe : {A : Set} → A → Maybe A → A
    maybe a nothing = a
    maybe _ (just a) = a

  -- natural
  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}

    add : ℕ → ℕ → ℕ
    add zero m = m
    add (succ n) m = succ (add n m)

    eqℕ : ℕ → ℕ → Bool
    eqℕ zero zero = true
    eqℕ zero (succ m) = false
    eqℕ (succ n) zero = false
    eqℕ (succ n) (succ m) = eqℕ n m

    leℕ : ℕ → ℕ → Bool
    leℕ zero m = true
    leℕ (succ n) zero = false
    leℕ (succ n) (succ m) = leℕ n m

  -- list
  module _ where
    infixr 5 _,_
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

    data _∈_ {A : Set} : A → List A → Set where
      here : ∀ {a as} → a ∈ (a , as)
      there : ∀ {a a' as} → a ∈ as → a ∈ (a' , as)

  -- decidable
  module _ where
    data Dec (A : Set) : Set where
      yes : A → Dec A
      no : (A → ⊥) → Dec A

    Dec2 : {A : Set} → (A → A → Set) → Set
    Dec2 {A} R = (x y : A) → Dec (R x y)

  -- sorted lists
  module _ (A : Set) (_≤_ : A → A → Set) where
    data _≤*_ : A → List A → Set where
      ε : ∀ {a as} → a ≤* as
      _,_ : ∀ {a a' as} → a ≤ a' → a ≤* as → a ≤* (a' , as)

    data IsSorted : List A → Set where
      ε : IsSorted ε
      _,_ : ∀ {a as} → a ≤* as → IsSorted as → IsSorted (a , as)

    record SortedList : Set where
      constructor mkSortedList
      field
        list : List A
        isSorted : IsSorted list

    record MergeResult (xs ys : List A) (sxs : IsSorted xs) (sys : IsSorted ys) : Set where
      constructor mkMergeResult
      field
        rs : List A
        isSorted : IsSorted rs
        p1 : {a : A} → a ≤* xs → a ≤* ys → a ≤* rs
        p2 : {a : A} → (a ∈ xs) + (a ∈ ys) → a ∈ rs
        p3 : {a : A} → a ∈ rs → (a ∈ xs) + (a ∈ ys)
        p4 : {a : A} → (k : (a ∈ xs) + (a ∈ ys)) → p3 (p2 k) ≡ k
        p5 : {a : A} → (i : a ∈ rs) → p2 (p3 i) ≡ i

    module _ (_≤?_ : Dec2 _≤_) where
      dmerge : (xs ys : List A) → (sxs : IsSorted xs) → (sys : IsSorted ys) → MergeResult xs ys sxs sys
      MergeResult.rs (dmerge ε ys ε _) = ys
      MergeResult.isSorted (dmerge ε _ ε sys) = sys
      MergeResult.p1 (dmerge ε _ ε _) = \r1 r2 → r2
      MergeResult.p2 (dmerge ε _ ε _) = \{ (inl ()) ; (inr i) → i }
      MergeResult.p3 (dmerge ε _ ε _) = \i → inr i
      MergeResult.p4 (dmerge ε _ ε _) = \{ (inl ()) ; (inr _) → refl }
      MergeResult.p5 (dmerge ε _ ε _) = \_ → refl
      MergeResult.rs (dmerge xs@(_ , _) ε (_ , _) ε) = xs
      MergeResult.isSorted (dmerge (_ , _) ε sxs@(_ , _) ε) = sxs
      MergeResult.p1 (dmerge (_ , _) ε (_ , _) ε) = \r1 r2 → r1
      MergeResult.p2 (dmerge (_ , _) ε (_ , _) ε) = \{ (inl i) → i ; (inr ()) }
      MergeResult.p3 (dmerge (_ , _) ε (_ , _) ε) = \i → inl i
      MergeResult.p4 (dmerge (_ , _) ε (_ , _) ε) = \{ (inl _) → refl ; (inr ()) }
      MergeResult.p5 (dmerge (_ , _) ε (_ , _) ε) = \_ → refl
      dmerge (x , _) (y , _) (_ , _) (_ , _) with x ≤? y
      dmerge (x , xs) ys' (x≤xs , sxs) sys' | yes x≤y with dmerge xs ys' sxs sys'
      dmerge (x , xs) (_ , _) (x≤xs , sxs) (_ , _) | yes x≤y | mkMergeResult rs isSorted p1 p2 p3 p4 p5 = mkMergeResult (x , rs) ((p1 x≤xs {!!}) , isSorted) {!!} {!!} {!!} {!!} {!!}
      dmerge _ _ _ _ | no x≰y = {!!}
    {-
      xs : SortedList A
      ys : SortedList A
      ∀ a b → Dec (a ≤ b)
      --
      rs : SortedList A
      ∀a. a ≤ xs ∧ a ≤ ys → a ≤ rs
      (∀a. a ∈ xs ∨ a ∈ ys →̃  a ∈ rs)
    -}
    lmerge : {A : Set} → (compare : A → A → Bool) → List A → List A → List A
    lmerge compare ε ys = ys
    lmerge compare xs@(_ , _) ε = xs
    lmerge compare (x , xs) (y , ys) with compare x y
    ... | true = x , lmerge compare xs (y , ys)
    ... | false = y , lmerge compare (x , xs) ys

  -- colist with result
  module _ where
    data ColistF (R : Set) (A : Set) (X : Set) : Set where
      end : R → ColistF R A X
      cons : A → X → ColistF R A X

    record Colist' (R : Set) (A : Set) : Set where
      coinductive
      field
        unrollColist : ColistF R A (Colist' R A)
    open Colist' public

    try : {R A : Set} → ℕ → Colist' R A → R + A
    try zero s with unrollColist s
    ... | end r = inl r
    ... | cons a _ = inr a
    try (succ n) s with unrollColist s
    ... | end r = inl r
    ... | cons a s' = try n s'
    

-- memory
module _ where
  Var : Set
  Var = String × ℕ

  eqVar : Var → Var → Bool
  eqVar (v1 ,, i1) (v2 ,, i2) = and (primStringEquality v1 v2) (eqℕ i1 i2)

  data Val : Set where
    undefined : Val
    number : ℕ → Val
    string : String → Val

  Mem : Set
  Mem = List (Var × Val)

  get : Mem → Var → Maybe Val
  get ε v = nothing
  get ((v' ,, e) , as) v = eqVar v' v € λ{ true → just e ; false → get as v }

  set : Mem → Var → Val → Mem
  set as v e = (v ,, e) , as


data ProgramF (A : Set) (X : Set) : Set where
  return : A → ProgramF A X
  read : Var → (Val → X) → ProgramF A X
  write : Var → Val → X → ProgramF A X
  fail : ProgramF A X

{-
return : A → Program A
read : Var → Program Val
write : Var → Val → Program ⊤
fail : Program A
-}

record Program (A : Set) : Set where
  coinductive
  constructor mkP
  field
    unroll : ProgramF A (Program A)
open Program public


step : {A X : Set} → ProgramF A X → Mem → Maybe A + X × Mem
step (return a) mem = inl (just a)
step (read v p) mem = inr (p (maybe undefined (get mem v)) ,, mem)
step (write v e p) mem = inr (p ,, set mem v e)
step fail _ = inl nothing

run : {A : Set} → Program A → Mem → Colist' (Maybe A) Mem
unrollColist (run p mem) with step (unroll p) mem
... | inl r = end r
... | inr (p' ,, mem') = cons mem' (run p' mem')

--unrollColist (run p mem) = (\{ (inl r) → end r ; (inr s) → cons s (run (fst s) (snd s)) }) (step p mem)

{-
merge sorted arrays a[alen] and b[blen]

i = 0, j = 0, k = 0
while true:
  if k == alen + blen:
    break
  else if j == blen or read a i <= read b j:
    write pr[k] a[i]
    i += 1
    k += 1
  else:  // i == blen or read a i > read b j
    write pr[k] b[j]
    j += 1
    k += 1
-}

-- util
module _ where
  readNumber : {A X : Set} → X → Var → (ℕ → X) → ProgramF A X
  readNumber x v p = read v \{ (number n) → p n ; _ → x }

  inc : {A : Set} → Var → Program A → Program A
  inc v cont =
    mkP (readNumber (mkP fail) v \v' → mkP (write v (number (succ v')) cont))

  compare : Val → Val → Bool
  compare (number n) (number m) = leℕ n m
  compare _ _ = false

module _ where
  module _ where
    i j k a alen b blen r : String
    i ="i" ; j ="j"; k ="k"; a ="a"; alen ="alen"; b ="b"; blen ="blen"; r ="r"

  {-# TERMINATING #-}
  merge : Program ⊤
  merge =
    mkP (write (i ,, 0) (number 0) (
    mkP (write (j ,, 0) (number 0) (
    mkP (write (k ,, 0) (number 0) (
    loop
    )))))) where
      mutual
        loop : Program ⊤
        unroll loop =
               readNumber (mkP fail) (alen ,, 0) \alen' →
          mkP (readNumber (mkP fail) (blen ,, 0) \blen' →
          mkP (readNumber (mkP fail) (k ,, 0) \k' →
          eqℕ (add alen' blen') k' € \
            { true → mkP (return tt)
            ; false →
                mkP (readNumber (mkP fail) (i ,, 0) \i' →
                mkP (readNumber (mkP fail) (j ,, 0) \j' →
                eqℕ i' alen' € \
                { true → getSecond
                ; false →
                  mkP (read (a ,, i') \ai' →
                  mkP (read (b ,, j') \bj' →
                  compare ai' bj' € \
                  { true → getFirst
                  ; false → getSecond
                  }))
                }))
            }))

        getFirst : Program ⊤
        getFirst =
          mkP (readNumber (mkP fail) (i ,, 0) \i' →
          mkP (readNumber (mkP fail) (k ,, 0) \k' →
          mkP (read (a ,, i') \ai' →
          mkP (write (r ,, k') ai' (
          inc (i ,, 0) (
          inc (k ,, 0)
          loop
          ))))))

        getSecond : Program ⊤
        getSecond =
          mkP (readNumber (mkP fail) (j ,, 0) \j' →
          mkP (readNumber (mkP fail) (k ,, 0) \k' →
          mkP (read (b ,, j') \bj' →
          mkP (write (r ,, k') bj' (
          inc (j ,, 0) (
          inc (k ,, 0)
          loop
          ))))))

  initmem : Mem
  initmem =
    ( (alen ,, 0) ,, number 3
    , (blen ,, 0) ,, number 4
    , (a ,, 0) ,, number 11
    , (a ,, 1) ,, number 71
    , (a ,, 2) ,, number 81
    , (b ,, 0) ,, number 19
    , (b ,, 1) ,, number 29
    , (b ,, 2) ,, number 89
    , (b ,, 3) ,, number 99
    , ε
    )
  
  test : {!!}
  test = run merge initmem

  _ : {!!}
  _ = {!try 105 test!}
