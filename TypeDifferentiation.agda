{-# OPTIONS --type-in-type #-}
-- 2019-05-16, calculus on types, setoids
module TypeDifferentiation where

-- lib
module _ where
  -- binary endorelations
  module _ where
    Rel : Set → Set
    Rel A = A → A → Set

    Reflexive : {A : Set} → Rel A → Set
    Reflexive {A} R = (a : A) → R a a

    Transitive : {A : Set} → Rel A → Set
    Transitive {A} R = {a b c : A} → R a b → R b c → R a c

    Symmetric : {A : Set} → Rel A → Set
    Symmetric {A} R = {a b : A} → R a b → R b a
  
  -- finite (co)products
  module _ where
    data ⊥ : Set where

    record ⊤ : Set where
      constructor tt

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    record _×_ (A B : Set) : Set where
      field
        fst : A
        snd : B
    open _×_ public

    _<+>_ : {A B : Set} → (A → Set) → (B → Set) → (A + B → Set)
    (P <+> Q) (inl a) = P a
    (P <+> Q) (inr b) = Q b

    record Both {A B : Set} (P : A → Set) (Q : B → Set) (p : A × B) : Set where
      field
        Fst : P (fst p)
        Snd : Q (snd p)

    data OneOf {A B : Set} (P : A → Set) (Q : B → Set) (p : A × B) : Set where
      Fst : P (fst p) → OneOf P Q p
      Snd : Q (snd p) → OneOf P Q p

  -- dependent pair
  module _ where
    record Σ (A : Set) (B : A → Set) : Set where
      constructor mkΣ
      field
        π₁ : A
        π₂ : B π₁
    open Σ public

  -- natural
  module _ where
    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

  -- fin
  module _ where
    data Fin : ℕ → Set where
      zero : {n : ℕ} → Fin (succ n)
      succ : {n : ℕ} → Fin n → Fin (succ n)

  -- list
  module _ where
    data List (A : Set) : Set where
      ε : List A
      _,_ : A → List A → List A

    data All {A : Set} (P : A → Set) : List A → Set where
      ε : All P ε
      _,_ : ∀ {a as} → P a → All P as → All P (a , as)

    data Any {A : Set} (P : A → Set) : List A → Set where
      here : ∀ {a as} → P a → Any P (a , as)
      there : ∀ {a as} → Any P as → Any P (a , as)

data Type : (n : ℕ) → Set where
  t⊥ t⊤ : {n : ℕ} → Type n
  _t+_ _t×_ : {n : ℕ} → Type n → Type n → Type n
  μ ν : {n : ℕ} → Type (succ n) → Type n

{-
! : Type → (Type →+ Type)
σ π : List Type →+ Type
μ ν : (Type →+ Type) →+ Type

μ-intr : F μF → μF
μ-elim : (X : Type) → (F X → X) → (μF → X)

ν-intr : (X : Type) → (X → F X) → (X → νF)
ν-elim : νF → F νF


- free structures
magma  ~~  non-empty binary tree
semigroup  ~~  
commutative semigroup  ~~  non-empty bag  ~~  ∑{n∈ℕ}xⁿ⁺¹/(n+1)! = exp x - 1
-- d (x. exp x - 1) = exp x
monoid  ~~ list  ~~  ∑{n∈ℕ}xⁿ = 1/(1-x)
-- d (x. 1/(1−x)) = (1/(1-x))² ~~ (x. list x × list x)
commutative monoid  ~~  unordered list (bag)  ~~  ∑{n∈ℕ}xⁿ/n! = exp x
-- d exp = exp
semilattice  ~~  non-empty finite set
bounded semilattice  ~~  finite set
group  ~~  
abelian group  ~~

-}


-- util
module _ where
  Not : Set → Set
  Not A = A → ⊥

-- setoids
module _ where
  record Setoid : Set₁ where
    field
      Ob : Set
      Eq : Ob → Ob → Set
  open Setoid public
  
  record ArrowOb (S T : Setoid) : Set₁ where
    field
      ar : Ob S → Ob T
      consistent : {s s' : Ob S} → Eq S s s' → Eq T (ar s) (ar s')
  open ArrowOb public

  infixr 10 _#_
  _#_ : {S T : Setoid} → ArrowOb S T → Ob S → Ob T
  _#_ = ar

  -- arrows
  module _ where
    Arrow$ : (S T : Setoid) → Setoid
    Ob (Arrow$ S T) = ArrowOb S T
    Eq (Arrow$ S T) f f' = (s s' : Ob S) → Eq S s s' → Eq T (ar f s) (ar f' s')

    infixr 5 _→#_
    _→#_ : (S T : Setoid) → Setoid
    _→#_ = Arrow$

    identity! : (S : Setoid) → Ob (Arrow$ S S)
    ar (identity! S) s = s
    consistent (identity! S) s=s' = s=s'

    compose! : {S T U : Setoid} → Ob (Arrow$ S T) → Ob (Arrow$ T U) → Ob (Arrow$ S U)
    ar (compose! f g) s = ar g (ar f s)
    consistent (compose! f g) s=s' = consistent g (consistent f s=s') 

    const! : {S T : Setoid} → (reflexive : Reflexive (Eq S)) → Ob (S →# (T →# S))
    ar (ar (const! refl) s) t = s
    consistent (ar (const! refl) s) t=t' = refl s
    consistent (const! refl) s=s' t t' t=t' = s=s'


  -- setoid of setoids
  module _ where
    -- setoid isomorphism
    record SetoidEq (S T : Setoid) : Set where
      field
        to : Ob (Arrow$ S T)
        from : Ob (Arrow$ T S)
        to▹from : Eq (Arrow$ S S) (compose! to from) (identity! S)
        from▹to : Eq (Arrow$ T T) (compose! from to) (identity! T)
    open SetoidEq public

    Setoid# : Setoid
    Ob Setoid# = Setoid
    Eq Setoid# S₁ S₂ = SetoidEq S₁ S₂

  -- finite (co)products
  module _ where
    ⊥# : Setoid
    Ob ⊥# = ⊥
    Eq ⊥# () ()

    ⊤# : Setoid
    Ob ⊤# = ⊤
    Eq ⊤# tt tt = ⊤

    data EitherEq (S T : Setoid) : (e₁ e₂ : Ob S + Ob T) → Set where
      inlEq : {s s' : Ob S} → Eq S s s' → EitherEq S T (inl s) (inl s')
      inrEq : {t t' : Ob T} → Eq T t t' → EitherEq S T (inr t) (inr t')

    Either$ : Setoid → Setoid → Setoid
    Ob (Either$ S T) = Ob S + Ob T
    Eq (Either$ S T) p₁ p₂ = EitherEq S T p₁ p₂

    record PairEq (S T : Setoid) (p₁ p₂ : Ob S × Ob T) : Set where
      field
        fstEq : Eq S (fst p₁) (fst p₂)
        sndEq : Eq T (snd p₁) (snd p₂)

    Pair$ : Setoid → Setoid → Setoid
    Ob (Pair$ S T) = Ob S × Ob T
    Eq (Pair$ S T) p₁ p₂ = Eq S (fst p₁) (fst p₂) × Eq T (snd p₁) (snd p₂)

  -- dependent (co)product
  module _ where
    IndexedSetoid$ : Setoid → Setoid
    IndexedSetoid$ S = Arrow$ S Setoid#

    Eq' : (S : Setoid) → (I : ArrowOb S Setoid#) → (s s' : Ob S) → (s=s' : Eq S s s') → (i : Ob (ar I s)) → (i' : Ob (ar I s')) → Set
    Eq' S I s s' s=s' i i' = Eq (ar I s) i (ar (from (consistent I s=s')) i')

    -- alternative
    Eq'2 : (S : Setoid) → (I : ArrowOb S Setoid#) → (s s' : Ob S) → (s=s' : Eq S s s') → (i : Ob (ar I s)) → (i' : Ob (ar I s')) → Set
    Eq'2 S I s s' s=s' i i' = Eq (ar I s') (ar (to (consistent I s=s')) i) i'

    ΣOb : (S : Setoid) → (I : Ob (IndexedSetoid$ S)) → Set
    ΣOb S I = Σ (Ob S) (\s → Ob (ar I s))

    record ΣEq (S : Setoid) (I : Ob (IndexedSetoid$ S)) (p p' : ΣOb S I) : Set where
      field
        π₁Eq : Eq S (π₁ p) (π₁ p')
        π₂Eq : Eq' S I (π₁ p) (π₁ p') π₁Eq (π₂ p) (π₂ p')

    Σ$ : (S : Setoid) → Ob (IndexedSetoid$ S) → Setoid
    Ob (Σ$ S I) = ΣOb S I
    Eq (Σ$ S I) p p' = ΣEq S I p p'

    Π$ : (S : Setoid) → Ob (IndexedSetoid$ S) → Setoid
    Ob (Π$ S I) = (s : Ob S) → Ob (ar I s)
    Eq (Π$ S I) f f' = (s s' : Ob S) → (s=s' : Eq S s s') → Eq' S I s s' s=s' (f s) (f s')


  Prop# : Setoid
  Ob Prop# = Set
  Eq Prop# A B = (A → B) × (B → A)

  SubtractOne$ : (S : Setoid) → (s : Ob S) → Setoid
  Ob (SubtractOne$ S s) = Σ (Ob S) (\s' → Not (Eq S s s'))
  Eq (SubtractOne$ S s) t t' = Eq S (π₁ t) (π₁ t')

  Quotient$ : (S T : Setoid) → Ob (Arrow$ S T) → Setoid
  Ob (Quotient$ S T f) = Ob S
  Eq (Quotient$ S T f) s s' = Eq T (ar f s) (ar f s')


  -- functor Setoid → Setoid
  record SetoidFunctor : Set where
    field
      mapOb : Ob (Setoid# →# Setoid#)
      mapAr : {S T : Setoid} → Ob ((S →# T) →# (mapOb # S →# mapOb # T))
      preservesId : {S : Setoid} → Eq (mapOb # S →# mapOb # S) (mapAr # identity! S) (identity! (mapOb # S))
      preservesCompose :
        {S T U : Setoid} → (f : Ob (S →# T)) → (g : Ob (T →# U))
        → Eq (mapOb # S →# mapOb # U) (mapAr # compose! f g) (compose! (mapAr # f) (mapAr # g))
  open SetoidFunctor public

  infixr 10 _%_
  _%_ : (F : SetoidFunctor) → Setoid → Setoid
  F % X = mapOb F # X

  infixr 10 _%%_
  _%%_ : {S T : Setoid} → (F : SetoidFunctor) → Ob (S →# T) → Ob (F % S →# F % T)
  F %% f = mapAr F # f

  record InitialAlgebra (F : SetoidFunctor) : Set where
    field
      μF  : Ob Setoid#
      con : Ob (F % μF →# μF)
      -- ind : Ob (Π$ Setoid# (\X → (F % X →# X) →# (μF →# X)))
      ind : (X : Setoid) → Ob ((F % X →# X) →# (μF →# X))
      _eq : (X : Setoid) → (f : Ob (F % X →# X)) → Eq (F % μF →# X) (compose! con (ind X # f)) (compose! (F %% ind X # f) f)

  record TerminalCoalgebra (F : SetoidFunctor) : Set where
    field
      νF  : Ob Setoid#
      dec : Ob (νF →# F % νF)
      coi : (X : Setoid) → Ob ((X →# F % X) →# (X →# νF))
      _eq : (X : Setoid) → (f : Ob (X →# F % X)) → Eq (X →# F % νF) (compose! (coi X # f) dec) (compose! f (F %% coi X # f))


  record InitialDialgebra (F G : SetoidFunctor) : Set where
    field
      μFG : Ob Setoid#
      _o1 : Ob (F % μFG →# G % μFG)
      _o2 : (X : Setoid) → Ob ((F % X →# G % X) →# (μFG →# X))
      _eq : (X : Setoid) → (f : Ob (F % X →# G % X)) → Eq (F % μFG →# G % X) (compose! _o1 (G %% _o2 X # f)) (compose! (F %% _o2 X # f) f)

  record TerminalDialgebra (F G : SetoidFunctor) : Set where
    field
      νFG : Ob Setoid#
      _o1 : Ob (F % νFG →# G % νFG)
      _o2 : (X : Setoid) → Ob ((F % X →# G % X) →# (X →# νFG))
      _eq : (X : Setoid) → (f : Ob (F % X →# G % X)) → Eq (F % X →# G % νFG) (compose! (F %% _o2 X # f) _o1) (compose! f (G %% _o2 X # f))
