module _ where

module _ where
  data ⊥ : Set where
  
  record ⊤ : Set where
    constructor tt

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  infixr 15 _×_
  infixr 5 _,_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B

  infixr 5 _,,_
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,,_
    field
      first : A
      second : B first

  infixr 10 _+_
  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  data Eq {A : Set} (a : A) : A → Set where
    refl : Eq a a

  _≡_ = Eq

  Pred : Set → Set₁
  Pred A = A → Set

  infixr 5 _∷_
  data List (A : Set) : Set where
    ε : List A
    _∷_ : A → List A → List A

  data All {A : Set} (P : A → Set) : List A → Set where
    ε : All P ε
    _∷_ : ∀ {a as} → P a → All P as → All P (a ∷ as)

  data All₁ {A : Set} (P : A → Set₁) : List A → Set₁ where
    ε : All₁ P ε
    _∷_ : ∀ {a as} → P a → All₁ P as → All₁ P (a ∷ as)

  data Any {A : Set} (P : A → Set) : List A → Set where
    here : ∀ {a as} → P a → Any P (a ∷ as)
    there : ∀ {a as} → Any P as → Any P (a ∷ as)

  {-
  data Has {A : Set} : List A → A → Set where
    here : ∀ {a as} → Has (a ∷ as) a
    there : ∀ {a b as} → Has as a → Has (b ∷ as) a
  -}
  Has : {A : Set} → List A → A → Set
  Has as a = Any (Eq a) as


  data AllAll {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → All P as → Set where
    ε : AllAll P2 ε
    _∷_ : ∀ {a as Pa Pas} → P2 Pa → AllAll P2 {as} Pas → AllAll P2 {a ∷ as} (Pa ∷ Pas)

  All× : {A B : Set} → (A → Set) → (B → Set) → (A × B → Set)
  All× P1 P2 (a , b) = P1 a × P2 b

  --AllAny : {A : Set} {P : A → Set} → (P2 : ∀ {a} → P a → Set) → (∀ {as} → Any P as → Set)
  --AllAny P2 (here Pa) = P2 Pa
  --AllAny P2 (there any-Pa) = AllAny P2 any-Pa
  --data AllAny {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → All P as → Set where
  data AllAny {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → Any P as → Set where
    here : ∀ {a as} {Pa : P a} → P2 Pa → AllAny P2 {a ∷ as} (here Pa)
    there : ∀ {a as} {any-Pa} → AllAny P2 {as} any-Pa → AllAny P2 {a ∷ as} (there any-Pa)

  data AllΣ {A : Set} {B : A → Set} (AllB : ∀ {a} → B a → Set) : Σ A B → Set where
    _,,_ : ∀ a {b : B a} → AllB b → AllΣ AllB (a ,, b)
  --AllΣ P (a ,, b) = P b

  transport : {A : Set} → (P : A → Set) → ∀ {a a'} → a ≡ a' → P a → P a'
  transport P refl Pa = Pa

  cong : {A B : Set} → (f : A → B) → ∀ {a a'} → a ≡ a' → f a ≡ f a'
  cong f refl = refl

  single : ∀ {A} → A → List A
  single a = a ∷ ε

  reverse : ∀ {A} → List A → List A
  reverse as = reverse' as ε where
    reverse' : ∀ {A} → List A → List A → List A
    reverse' cs ε = cs
    reverse' cs (a ∷ as) = reverse' (a ∷ cs) as

  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  Has++l : ∀ {Ω : Set} → ∀ {τs τ} ρs → Has {Ω} τs τ → Has (ρs ++ τs) τ
  Has++l ε i = i
  Has++l (x ∷ ρs) i = there (Has++l ρs i)

  Has++r : ∀ {Ω : Set} → ∀ {τ ρs} → Has {Ω} ρs τ → (τs : List Ω) → Has (ρs ++ τs) τ
  Has++r (here x) τs = here x
  Has++r (there i) τs = there (Has++r i τs)

  succc* : {A : Set} {as as' : List A} → (∀ {r} → Has as r → Has as' r) → (cs : List A) → (∀ {r} → Has (cs ++ as) r → Has (cs ++ as') r)
  succc* f ε x = f x
  succc* f (c ∷ cs) (here x) = here x
  succc* f (c ∷ cs) (there x) = there (succc* f cs x)

  $0 : ∀ {A a0 as} → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as} → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2

  single' : {A : Set} {P : A → Set} {a : A} → P a → All P (single a)
  single' Pa = Pa ∷ ε

  _++'_ : {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
  ε ++' Pys = Pys
  (Px ∷ Pxs) ++' Pys = Px ∷ (Pxs ++' Pys)

  mapList : {A B : Set} → (A → B) → (List A → List B)
  mapList f ε = ε
  mapList f (a ∷ as) = f a ∷ mapList f as

  mapAll : {A : Set} {P Q : A → Set} → (∀ {a} → P a → Q a) → (∀ {as} → All P as → All Q as)
  mapAll f ε = ε
  mapAll f (Pa ∷ Pas) = f Pa ∷ mapAll f Pas

  mapAny : {A : Set} {P Q : A → Set} → (∀ {a} → P a → Q a) → (∀ {as} → Any P as → Any Q as)
  mapAny f (here Pa) = here (f Pa)
  mapAny f (there Pas) = there (mapAny f Pas)

  mapAnyAll : {A R : Set} {P : A → Set} {as : List A} → Any P as → All (\a → P a → R) as → R
  mapAnyAll (here Pa) (fa ∷ fas) = fa Pa
  mapAnyAll (there Pas) (fa ∷ fas) = mapAnyAll Pas fas

  --mapAllAny : {A R : Set} {P : A → Set} {as : List A} → All P as → Any (\a → P a → R) as → R
  --mapAllAny (Pa ∷ Pas) (here fa)   = fa Pa
  --mapAllAny (Pa ∷ Pas) (there fas) = mapAllAny Pas fas

  getAllAny : {A R : Set} {P Q : A → Set} → (∀ {a} → P a → Q a → R) → (∀ {as} → All P as → Any Q as → R)
  getAllAny f (Pa ∷ Pas) (here Qa) = f Pa Qa
  getAllAny f (Pa ∷ Pas) (there any-Q) = getAllAny f Pas any-Q

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get all-p any-eq = getAllAny (\{ Pa refl → Pa }) all-p any-eq

  _++2_ : ∀ {A P xs ys Pxs Pys} {P2 : {a : A} → P a → Set} → AllAll P2 {xs} Pxs → AllAll P2 {ys} Pys → AllAll {A} {P} P2 {xs ++ ys} (Pxs ++' Pys)
  ε ++2 Pys = Pys
  (Px ∷ Pxs) ++2 Pys = Px ∷ (Pxs ++2 Pys)

  get2 : ∀ {A P a as Pas} → {P2 : ∀ {a} → P a → Set} → AllAll {A} {P} P2 {as} Pas → (i : Has as a) → P2 (get Pas i)
  get2 (x ∷ x₁) (here refl) = x
  get2 (x ∷ x₁) (there i) = get2 x₁ i

  map× : {A1 B1 A2 B2 : Set} → (A1 → A2) → (B1 → B2) → A1 × B1 → A2 × B2
  map× f g (a , b) = f a , g b

  mapΣ : {A : Set} {B1 B2 : A → Set} → (∀ {a} → B1 a → B2 a) → Σ A B1 → Σ A B2
  mapΣ f (a ,, b) = (a ,, f b)

  mapAllAll :
    {A : Set} {P : A → Set} {P2 Q2 : ∀ {a} → P a → Set}
    → (∀ {a} → {Pa : P a} → P2 Pa → Q2 Pa) → ∀ {as} → {Pas : All P as} → AllAll P2 Pas → AllAll Q2 Pas
  mapAllAll f ε = ε
  mapAllAll f (P2Pa ∷ P2Pas) = f P2Pa ∷ mapAllAll f P2Pas

  buildAllAll : {A : Set} {P : A → Set} → {P2 : ∀ {a} → P a → Set} → (f : ∀ {a} → (Pa : P a) → P2 Pa) → ∀ {as} → (Pas : All P as) → AllAll P2 Pas
  buildAllAll f ε = ε
  buildAllAll f (x ∷ as) = f x ∷ buildAllAll f as

  buildAllAny : {A : Set} {P : A → Set} → {P2 : ∀ {a} → P a → Set} → (f : ∀ {a} → (Pa : P a) → P2 Pa) → ∀ {as} → (any-P : Any P as) → AllAny P2 any-P
  buildAllAny f (here Pa) = here (f Pa)
  buildAllAny f (there any-P) = there (buildAllAny f any-P)

  identity : {A : Set} → A → A
  identity a = a

  allMapAll : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : ∀ {a} → P1 a → Set) → (AllP2 : ∀ {a} → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 P1a → AllP2 (mapP P1a)) → ∀ {as} {P1as : All P1 as} → AllAll AllP1 P1as → AllAll AllP2 (mapAll mapP P1as)
  allMapAll mapP AllP1 AllP2 allMapP ε = ε
  allMapAll mapP AllP1 AllP2 allMapP (allPa ∷ allAllPas) = allMapP allPa ∷ allMapAll mapP AllP1 AllP2 allMapP allAllPas

  allMapAny : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : ∀ {a} → P1 a → Set) → (AllP2 : ∀ {a} → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 P1a → AllP2 (mapP P1a)) → ∀ {as} {any-P1 : Any P1 as} → AllAny AllP1 any-P1 → AllAny AllP2 (mapAny mapP any-P1)
  allMapAny mapP AllP1 AllP2 allMapP (here z) = here (allMapP z)
  allMapAny mapP AllP1 AllP2 allMapP (there z) = there (allMapAny mapP AllP1 AllP2 allMapP z)

  allMap× : {A1 B1 A2 B2 : Set} → (mapA : A1 → A2) → (mapB : B1 → B2) → (P1 : A1 → Set) (P2 : A2 → Set) (Q1 : B1 → Set) (Q2 : B2 → Set) → (allMapA : ∀ {a} → P1 a → P2 (mapA a)) → (allMapB : ∀ {b} → Q1 b → Q2 (mapB b)) → ({t : A1 × B1} → All× P1 Q1 t → All× P2 Q2 (map× mapA mapB t))
  allMap× mapA mapB P1 P2 Q1 Q2 allMapA allMapB (a , b) = allMapA a , allMapB b

  allMapΣ : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : ∀ {a} → P1 a → Set) → (AllP2 : ∀ {a} → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 P1a → AllP2 (mapP P1a)) → ({t : Σ A P1} → AllΣ AllP1 t → AllΣ AllP2 (mapΣ mapP t))
  allMapΣ mapP AllP1 AllP2 allMapP (a ,, Pa) = a ,, allMapP Pa

  --allMap× : {A B : Set} {P1 P2 : A → Set} {Q1 Q2 : B → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (mapQ : ∀ {b} → Q1 b → Q2 b) → (AllP1 : ∀ {a} → P1 a → Set) → (AllP2 : ∀ {a} → P2 a → Set) → (AllQ1 : ∀ {b} → Q1 b → Set) → (AllQ2 : ∀ {b} → Q2 b → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 P1a → AllP2 (mapP P1a)) → (allMapQ : ∀ {b} {Q1b : Q1 b} → AllQ1 Q1b → AllQ2 (mapQ Q1b)) → ({t : A × B} → All× AllP1 AllQ1 t → All× AllP2 AllQ2 (map× mapP mapQ t))
  --allMap× mapP AllP1 AllP2 allMapP (a ,, Pa) = a ,, allMapP Pa

-- types
module _ where
  data Type : Set where
    _⇒*_ : List Type → Type → Type
    #Sum : List Type → Type
    #Product : List Type → Type
    #Nat : Type
    #List : Type → Type
    #Tree : Type → Type
    #Conat : Type
    --#Delay : Type → Type
    --#Colist : Type → Type
    #Stream : Type → Type

  infixr 5 _⇒_
  _⇒_ : Type → Type → Type
  σ ⇒ τ = single σ ⇒* τ
  
  #Void : Type
  #Void = #Sum ε
  
  #Unit : Type
  #Unit = #Product ε
  
  #Either : Type → Type → Type
  #Either σ τ = #Sum (σ ∷ τ ∷ ε)
  
  #Pair : Type → Type → Type
  #Pair σ τ = #Product (σ ∷ τ ∷ ε)

  #Bool : Type
  #Bool = #Either #Unit #Unit
  
  #Maybe : Type → Type
  #Maybe τ = #Either #Unit τ

data IntrF (%Function : List Type → Type → Set) (%Value : Type → Set) : Type → Set where
  intrArrow   : ∀ {ρs τ} → %Function ρs τ                                  → IntrF %Function %Value (ρs ⇒* τ)
  intrSum     : ∀ {τs}   → Any %Value τs                                   → IntrF %Function %Value (#Sum τs)
  intrProduct : ∀ {τs}   → All %Value τs                                   → IntrF %Function %Value (#Product τs)
  intrNat     :            %Value (#Maybe #Nat)                            → IntrF %Function %Value  #Nat
  intrList    : ∀ {τ}    → %Value (#Maybe (#Pair τ (#List τ)))             → IntrF %Function %Value (#List τ)
  intrTree    : ∀ {τ}    → %Value (#Either τ (#Pair τ (#Pair (#Tree τ) (#Tree τ)))) → IntrF %Function %Value (#Tree τ)
  intrConat   :            Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Maybe ρ))  → IntrF %Function %Value  #Conat
  intrStream  : ∀ {τ}    → Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Pair τ ρ)) → IntrF %Function %Value (#Stream τ)

data ElimF (%Value : Type → Set) : Type → Type → Set where
  elimArrow   : ∀ {ρs τ} → All %Value ρs                                → ElimF %Value (ρs ⇒* τ)     τ
  elimSum     : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs                 → ElimF %Value (#Sum τs)     ϕ
  elimProduct : ∀ {τs ϕ} → Any (\τ → %Value (τ ⇒ ϕ)) τs                 → ElimF %Value (#Product τs) ϕ
  elimNat     : ∀ {ϕ}    → %Value (#Maybe ϕ ⇒ ϕ)                        → ElimF %Value  #Nat         ϕ
  elimList    : ∀ {τ ϕ}  → %Value (#Maybe (#Pair τ ϕ) ⇒ ϕ)              → ElimF %Value (#List τ)     ϕ
  elimTree    : ∀ {τ ϕ}  → %Value (#Either τ (#Pair τ (#Pair ϕ ϕ)) ⇒ ϕ) → ElimF %Value (#Tree τ)     ϕ
  elimConat   :                                                           ElimF %Value  #Conat      (#Maybe #Conat)
  elimStream  : ∀ {τ}                                                   → ElimF %Value (#Stream τ)  (#Pair τ (#Stream τ))

data ExprF (%F : List Type → Type → Set) (%V : Type → Set) (τ : Type) : Set where
  intr : IntrF %F %V τ               → ExprF %F %V τ
  elim : ∀ {ϕ} → %V ϕ → ElimF %V ϕ τ → ExprF %F %V τ

module _ where
  module _
      {%F1 %F2 : List Type → Type → Set} (%mapF : ∀ {ρs τ} → %F1 ρs τ → %F2 ρs τ)
      {%V1 %V2 : Type → Set} (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    where
  
    mapIntrF : ∀ {τ} → IntrF %F1 %V1 τ → IntrF %F2 %V2 τ
    mapIntrF (intrArrow rule)   = intrArrow   (%mapF rule)
    mapIntrF (intrSum rule)     = intrSum     (mapAny %mapV rule)
    mapIntrF (intrProduct rule) = intrProduct (mapAll %mapV rule)
    mapIntrF (intrNat rule)     = intrNat     (%mapV rule)
    mapIntrF (intrList rule)    = intrList    (%mapV rule)
    mapIntrF (intrTree rule)    = intrTree    (%mapV rule)
    mapIntrF (intrConat rule)   = intrConat   (mapΣ (map× %mapV %mapV) rule)
    mapIntrF (intrStream rule)  = intrStream  (mapΣ (map× %mapV %mapV) rule)
  
  module _ {%V1 %V2 : Type → Set} (%mapV : ∀ {τ} → %V1 τ → %V2 τ) where
    mapElimF : ∀ {τ ϕ} → ElimF %V1 τ ϕ → ElimF %V2 τ ϕ
    mapElimF (elimArrow rule)   = elimArrow   (mapAll %mapV rule)
    mapElimF (elimSum rule)     = elimSum     (mapAll %mapV rule)
    mapElimF (elimProduct rule) = elimProduct (mapAny %mapV rule)
    mapElimF (elimNat rule)     = elimNat     (%mapV rule)
    mapElimF (elimList rule)    = elimList    (%mapV rule)
    mapElimF (elimTree rule)    = elimTree    (%mapV rule)
    mapElimF  elimConat         = elimConat
    mapElimF  elimStream        = elimStream

  module _
      {%F1 %F2 : List Type → Type → Set} (%mapF : ∀ {ρs τ} → %F1 ρs τ → %F2 ρs τ)
      {%V1 %V2 : Type → Set} (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    where
  
    mapExprF : ∀ {τ} → ExprF %F1 %V1 τ → ExprF %F2 %V2 τ
    mapExprF (intr rule)       = intr (mapIntrF %mapF %mapV rule)
    mapExprF (elim value rule) = elim (%mapV value) (mapElimF %mapV rule)

  module _
      {%F : List Type → Type → Set} (%AllF : ∀ {ρs τ} → %F ρs τ → Set)
      {%V : Type → Set} (%AllV : ∀ {τ} → %V τ → Set)
    where
    AllIntrF : ∀ {τ} → IntrF %F %V τ → Set
    AllIntrF (intrArrow rule)   = %AllF rule
    AllIntrF (intrSum rule)     = AllAny %AllV rule
    AllIntrF (intrProduct rule) = AllAll %AllV rule
    AllIntrF (intrNat rule)     = %AllV rule
    AllIntrF (intrList rule)    = %AllV rule
    AllIntrF (intrTree rule)    = %AllV rule
    AllIntrF (intrConat rule)   = AllΣ (All× %AllV %AllV) rule
    AllIntrF (intrStream rule)  = AllΣ (All× %AllV %AllV) rule

  module _ {%V : Type → Set} (%AllV : ∀ {τ} → %V τ → Set) where
    AllElimF : ∀ {τ ϕ} → ElimF %V τ ϕ → Set
    AllElimF (elimArrow rule)   = AllAll %AllV rule
    AllElimF (elimSum rule)     = AllAll %AllV rule
    AllElimF (elimProduct rule) = AllAny %AllV rule
    AllElimF (elimNat rule)     = %AllV rule
    AllElimF (elimList rule)    = %AllV rule
    AllElimF (elimTree rule)    = %AllV rule
    AllElimF  elimConat         = ⊤
    AllElimF  elimStream        = ⊤

  module _
      {%F : List Type → Type → Set} (%AllF : ∀ {ρs τ} → %F ρs τ → Set)
      {%V : Type → Set} (%AllV : ∀ {τ} → %V τ → Set)
    where
    data AllExprF : ∀ {τ} → ExprF %F %V τ → Set where
      mkAllIntr : ∀ {τ} {rule : IntrF %F %V τ} → AllIntrF %AllF %AllV rule → AllExprF (intr rule)
      mkAllElim : ∀ {ρ τ} {value : %V ρ} {rule : ElimF %V ρ τ} → %AllV value → AllElimF %AllV rule → AllExprF (elim value rule)

  module _
      {%F1 %F2 : List Type → Type → Set}
      (%mapF : ∀ {ρs τ} → %F1 ρs τ → %F2 ρs τ)
      (%AllF1 : ∀ {ρs τ} → %F1 ρs τ → Set)
      (%AllF2 : ∀ {ρs τ} → %F2 ρs τ → Set)
      (%allMapF : ∀ {ρs τ} {f1 : %F1 ρs τ} → %AllF1 f1 → %AllF2 (%mapF f1))

      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ {τ} → %V1 τ → Set)
      (%AllV2 : ∀ {τ} → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 v1 → %AllV2 (%mapV v1))
    where
    allMapIntrF : ∀ {τ} → (intr1 : IntrF %F1 %V1 τ) → AllIntrF %AllF1 %AllV1 intr1 → AllIntrF %AllF2 %AllV2 (mapIntrF %mapF %mapV intr1)
    allMapIntrF (intrArrow rule)   all = %allMapF all
    allMapIntrF (intrSum rule)     all = allMapAny %mapV _ _{-_%AllV1 %AllV2-} %allMapV all
    allMapIntrF (intrProduct rule) all = allMapAll %mapV _ _{-%AllV1 %AllV2-} %allMapV all
    allMapIntrF (intrNat rule)     all = %allMapV all
    allMapIntrF (intrList rule)    all = %allMapV all
    allMapIntrF (intrTree rule)    all = %allMapV all
    allMapIntrF (intrConat rule)   all = allMapΣ (map× %mapV %mapV) _{-(All× %AllV1 %AllV1)-} _{-(All× %AllV2 %AllV2)-} (allMap× %mapV %mapV %AllV1 %AllV2 %AllV1 %AllV2 %allMapV %allMapV) all
    allMapIntrF (intrStream rule)  all = allMapΣ (map× %mapV %mapV) _{-(All× %AllV1 %AllV1)-} _{-(All× %AllV2 %AllV2)-} (allMap× %mapV %mapV %AllV1 %AllV2 %AllV1 %AllV2 %allMapV %allMapV) all

  module _
      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ {τ} → %V1 τ → Set)
      (%AllV2 : ∀ {τ} → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 v1 → %AllV2 (%mapV v1))
    where
    allMapElimF : ∀ {τ ϕ} → (elim1 : ElimF %V1 τ ϕ) → AllElimF %AllV1 elim1 → AllElimF %AllV2 (mapElimF %mapV elim1)
    allMapElimF (elimArrow rule)   all = allMapAll %mapV _ _ %allMapV all
    allMapElimF (elimSum rule)     all = allMapAll %mapV _ _ %allMapV all 
    allMapElimF (elimProduct rule) all = allMapAny %mapV _ _ %allMapV all 
    allMapElimF (elimNat rule)     all = %allMapV all 
    allMapElimF (elimList rule)    all = %allMapV all 
    allMapElimF (elimTree rule)    all = %allMapV all 
    allMapElimF  elimConat         all = all
    allMapElimF  elimStream        all = all

  module _ {%V : Type → Set} {%PredV : ∀ {τ} → %V τ → Set} (%allV : ∀ {τ} → (v : %V τ) → %PredV v) where
    buildAllElim : ∀ {τ ϕ} → (rule : ElimF %V τ ϕ) → AllElimF %PredV rule
    buildAllElim (elimArrow rule)   = buildAllAll %allV rule
    buildAllElim (elimSum rule)     = buildAllAll %allV rule
    buildAllElim (elimProduct rule) = buildAllAny %allV rule
    buildAllElim (elimNat rule)     = %allV rule
    buildAllElim (elimList rule)    = %allV rule
    buildAllElim (elimTree rule)    = %allV rule
    buildAllElim  elimConat         = tt
    buildAllElim  elimStream        = tt

module _ where
  mutual
    -- regular de-bruijn term
    data Term (Γ : List Type) (τ : Type) : Set where
      var  : Has Γ τ → Term Γ τ
      wrap : ExprF (TermAbs Γ) (Term Γ) τ → Term Γ τ
  
    TermAbs : List Type → (List Type → Type → Set)
    TermAbs Γ σs τ = Term (σs ++ Γ) τ

  {-# TERMINATING #-}
  mapTerm : ∀ {Γ Δ} → (∀ {τ} → Has Γ τ → Has Δ τ) → (∀ {τ} → Term Γ τ → Term Δ τ)
  mapTerm f (var x) = var (f x)
  mapTerm f (wrap expr) = wrap (mapExprF (\{ρs} → mapTerm (succc* f ρs)) (mapTerm f) expr)

  #lambda : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  #lambda f = wrap (intr (intrArrow f))

  #apply : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  #apply f a = wrap (elim f (elimArrow (a ∷ ε)))
  
  #inl : ∀ {Γ σ τ} → Term Γ σ → Term Γ (#Either σ τ)
  #inl value = wrap (intr (intrSum (here value)))
  
  #inr : ∀ {Γ σ τ} → Term Γ τ → Term Γ (#Either σ τ)
  #inr value = wrap (intr (intrSum (there (here value))))
  
  #unit : ∀ {Γ} → Term Γ #Unit
  #unit = wrap (intr (intrProduct ε))
  
  #pair : ∀ {Γ σ τ} → Term Γ σ → Term Γ τ → Term Γ (#Pair σ τ)
  #pair value1 value2 = wrap (intr (intrProduct (value1 ∷ value2 ∷ ε)))

  #nothing : ∀ {Γ τ} → Term Γ (#Maybe τ)
  #nothing = #inl #unit

  #just : ∀ {Γ τ} → Term Γ τ → Term Γ (#Maybe τ)
  #just a = #inr a
  
  #zero : ∀ {Γ} → Term Γ #Nat
  #zero = wrap (intr (intrNat (#inl #unit)))
  
  #succ : ∀ {Γ} → Term Γ #Nat → Term Γ #Nat
  #succ n = wrap (intr (intrNat (#inr n)))
  
  #nil : ∀ {Γ τ} → Term Γ (#List τ)
  #nil = wrap (intr (intrList (#inl #unit)))
  
  #cons : ∀ {Γ τ} → Term Γ τ → Term Γ (#List τ) → Term Γ (#List τ)
  #cons head tail = wrap (intr (intrList (#inr (#pair head tail))))

  &either : ∀ {Γ σ τ ϕ} → Term Γ (σ ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Either σ τ) → Term Γ ϕ
  &either f s e = wrap (elim e (elimSum (f ∷ s ∷ ε)))

  &maybe : ∀ {Γ τ ϕ} → Term Γ (#Unit ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Maybe τ) → Term Γ ϕ
  &maybe n j m = wrap (elim m (elimSum (n ∷ j ∷ ε)))

  succt : ∀ {Γ ρ τ} → Term Γ τ → Term (ρ ∷ Γ) τ
  succt term = mapTerm there term

  &foldNat : ∀ {Γ ϕ} → Term Γ ϕ → Term Γ (ϕ ⇒ ϕ) → Term Γ #Nat → Term Γ ϕ
  &foldNat z s n = wrap (elim n (elimNat (#lambda (&maybe (#lambda (succt (succt z))) (succt s) (var $0)))))

  &foldNat' : ∀ {Γ ϕ} → Term Γ (#Maybe ϕ ⇒ ϕ) → Term Γ #Nat → Term Γ ϕ
  &foldNat' st n = wrap (elim n (elimNat st))

  #mapMaybe : ∀ {Γ σ τ} → Term Γ ((σ ⇒ τ) ⇒ (#Maybe σ ⇒ #Maybe τ))
  #mapMaybe = #lambda (#lambda (&maybe (#lambda #nothing) (#lambda (#just (#apply (var $2) (var $0)))) (var $0)))

  #elimNat : ∀ {Γ ϕ} → Term Γ ((#Maybe ϕ ⇒ ϕ) ⇒ (#Nat ⇒ ϕ))
  #elimNat = #lambda (#lambda (&foldNat' (var $1) (var $0)))

-- compiled representation
module _ where
  mutual
    data TermM (Γ : List Type) (τ : Type) : Set where
      return : Has Γ τ → TermM Γ τ
      set    : ∀ ρ → ExprF (TermMAbs Γ) (Has Γ) ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ

    TermMAbs : List Type → (List Type → Type → Set)
    TermMAbs Γ σs τ = TermM (σs ++ Γ) τ

  IntrM : List Type → Type → Set
  IntrM Γ τ = IntrF (TermMAbs Γ) (Has Γ) τ

  ElimM : List Type → Type → Type → Set
  ElimM Γ τ ϕ = ElimF (Has Γ) τ ϕ

  ExprM : List Type → Type → Set
  ExprM Γ τ = ExprF (TermMAbs Γ) (Has Γ) τ

  infixr 5 _▸_
  _▸_ : ∀ {Γ ρ τ} → ExprM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  _▸_ = set _

  pure : ∀ {Γ τ} → ExprM Γ τ → TermM Γ τ
  pure expr = set _ expr (return $0)

  {-
  combine2' : ∀ {Γ ρ τ} → TermM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  combine2' (return x) term2 = mapTermM (sterm x) term2
  combine2' (set ρ x term1) term2 = set ρ x (combine2 term1 (mapTermM sterma term2))

  combine : ∀ {Γ τ} → ∀ cs → ∀ {ρs} → All (TermM Γ) ρs → ExprF (TermMAbs Γ) (Has (ρs ++ cs)) τ → TermM Γ τ
  combine cs ε expr = pure (mapExprF identity {!!} expr)
  combine cs (term ∷ terms) expr = combine2 term {!!}
  -}

  {-
    Abs T Γ ρs τ = T (ρs ++ Γ) τ

    Term = μT. λΓτ. Has Γ + ExprF (Abs T Γ) (T Γ)
    TermM = μT. λΓτ. Has Γ + (ρ : Type) × ExprF (Abs T Γ) (Has Γ) × T (ρ ∷ Γ) τ
    
    ExprF (Abs Term Γ) (Term Γ) τ → ExprF (Abs TermM Γ) (TermM Γ) τ
    
    ExprF %F %V τ → (ρs : List Type) × All %V ρs × ExprF %F (Has ρs) τ
    EpxrF %F %V τ → Linear %F %V τ

    (ρs : List Type) × All (TermM Γ) ρs × ExprF (Abs TermM Γ) (Has ρs) τ → TermM Γ τ
    
    ε : ExprF %F (Has Γ) τ → Linear Γ τ
    _∷_ : %V ρ → Linear ρs τ → Linear (ρ ∷ ρs) τ

    TermF ? (TermM Γ) τ → (Δ : List Type) × ExprF ? (Has Δ) τ
    All (TermM Γ) τs
  -}

  {-
  data Linear' {Ω : Set} (%V : List Ω → Ω → Set) (%E : List Ω → Set) : List Ω → Set where
    ε : ∀ {ρs} → %E ρs → Linear' %V %E ρs
    _∷_ : ∀ {ρ ρs} → %V ρs ρ → Linear' %V %E ρs → Linear' %V %E (ρ ∷ ρs)

  LinearK : (%F : List Type → Type → Set) (%V : Type → Set) → Type → Set
  LinearK %F %V τ = Linear' (\ρs ρ → %V ρ) (\ϕs → ExprF %F (Has ϕs) τ) ε

  TermM' : (%F : List Type → Type → Set) → List Type → Type → Set
  TermM' %F Γ τ = Linear' (\ρs ρ → ExprF (\ϕs ϕ → %F (ϕs ++ Γ) ϕ) (Has ρs) ρ) (\ρs → Has ρs τ) Γ
  -}

  data Linear {Ω : Set} (%V : Ω → Set) (%E : List Ω → Set) : List Ω → Set where
    pureLinear : ∀ {ρs} → %E ρs → Linear %V %E ρs
    _∷_ : ∀ {ρ ρs} → %V ρ → Linear %V %E (ρ ∷ ρs) → Linear %V %E ρs
  -- %V ρ₁, L (ρ₁ ∷ ρs)
  --        %V ρ₂, L (ρ₂ ∷ ρ₁ ∷ ρs)
  -- %V ρ₁, %V ρ₂, …, %V ρₙ, %E [ρₙ,…,ρ₁]

  data Linear' {Ω : Set} (%V : Ω → Set) (%E : List Ω → Set) : Set where
    pureLinear' : %E ε → Linear' %V %E
    _∷_ : ∀ {ρ} → %V ρ → Linear' %V (\ρs → %E (ρ ∷ ρs)) → Linear' %V %E
  -- %V ρ₁, L (\ρs → %E (ρ₁ ∷ ρs))
  --        %V ρ₂, L (\ρs → ρ₂ ∷ %E' ρs)
  --        %V ρ₂, L (\ρs → ρ₂ ∷ ρ₁ ∷ ρs)
  -- %V ρ₁, %V ρ₂, …, %V ρₙ, %E [ρₙ,…,ρ₁]


  module _ {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} where
    mapLinear : (∀ {τs} → %E1 τs → %E2 τs) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 τs)
    mapLinear f (pureLinear x) = pureLinear (f x)
    mapLinear f (value ∷ linear) = value ∷ mapLinear f linear

    mapLinear' : ∀ Γ → ((τs : List Ω) → %E1 τs → %E2 (τs ++ Γ)) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 (τs ++ Γ))
    mapLinear' Γ f {τs} (pureLinear x) = pureLinear (f τs x)
    mapLinear' Γ f (v ∷ l) = v ∷ mapLinear' Γ f l

  -- %V ρ₁, …, %V ρₙ, (∀ {τs} → %E1 τs → %E2 (τs ++ ρsʳ ++ Γ))
  -- %V τ₁, …, %V τₖ, %E1 [τₖ…τ₁]
  -- → %V ρ₁, …, %V ρₙ, %V τ₁, …, %V τₖ, %E2 [τₖ…τ₁,ρₙ…ρ₁,Γ]
  module _ {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} where
    apLinear' : ∀ Γ → Linear %V (\ρs → (τs : List Ω) → %E1 τs → %E2 (τs ++ ρs)) Γ → Linear %V %E1 ε → Linear %V %E2 Γ
    apLinear' Γ (pureLinear f) l2 = mapLinear' Γ f l2 
    apLinear' Γ (_∷_ {σ} v l1) l2 = v ∷ apLinear' (σ ∷ Γ) l1 l2

    --apLinear : Linear %V (\ρs → ∀ {τs} → %E1 (τs ++ ρs) → %E2 (τs ++ ρs)) ε → Linear %V %E1 ε → Linear %V %E2 ε
    apLinear : Linear %V (\ρs → (τs : List Ω) → %E1 τs → %E2 (τs ++ ρs)) ε → Linear %V %E1 ε → Linear %V %E2 ε
    apLinear l1 l2 = apLinear' ε l1 l2

  data SinglePred {Ω : Set} (ω : Ω) : List Ω → Set where
    mkSinglePred : SinglePred ω (ω ∷ ε)

  module _ {Ω : Set} {%V : Ω → Set} where
    singleLinear : ∀ {ρ} → %V ρ → Linear %V (SinglePred ρ) ε
    singleLinear {ρ} v = v ∷ pureLinear mkSinglePred

  module _ {Ω : Set} {%V : Ω → Set} {%E : List Ω → Set} where
    singleLinear' : ∀ {ρ} → %V ρ → %E (ρ ∷ ε) → Linear %V %E ε
    singleLinear' {ρ} v e = v ∷ pureLinear e

  {-
  -- [σs] ↦ %V ρ₁, %V ρ₂, …, %V ρₙ, %E ([ρₙ,…,ρ₁] ++ σs)
  module _ {Ω : Set} {%V : Ω → Set} {%E : List Ω → Set} where
    moveLinear' : ∀ σ {Γ ρ} → Linear %V (\ρs → %E (ρ ∷ ρs)) (σ ∷ Γ) → Linear %V %E (σ ∷ ρ ∷ Γ)
    moveLinear' σ (pureLinear x) = pureLinear {!x!}
    moveLinear' σ (_∷_ {σ'} x l) = x ∷ {!moveLinear' σ' l!}

    -- moveLinear : ∀ {ρ} → Linear %V (\ρs → %E (ρ ∷ ρs)) ε → Linear %V %E (ρ ∷ ε)
    -- moveLinear : ∀ Γ {ρ} → Linear %V (\ρs → %E (ρ ∷ ρs)) Γ → Linear %V %E (ρ ∷ Γ)
    -- moveLinear : ∀ Γ {ρ} → Linear %V (\ρs → %E (ρ ∷ (Γ ++ ρs))) ε → Linear %V %E (ρ ∷ Γ)
    ------moveLinear : ∀ Γ Δ → Linear %V (\ρs → %E (Δ ++ ρs)) Γ → Linear %V %E (Δ ++ Γ)
    moveLinear : ∀ {ρ} → Linear %V (\ρs → %E (ρ ∷ ρs)) ε → Linear %V %E (ρ ∷ ε)
    moveLinear (pureLinear x) = pureLinear x
    --moveLinear (_∷_ {σ} x l) = x ∷ moveLinear' σ l 
    moveLinear (_∷_ {σ} x l) = x ∷ {!!}

    -- _∷_ : ∀ {ρ} → %V ρ → Linear' %V (\ρs → %E (ρ ∷ ρs)) → Linear' %V %E
    appendLinear : ∀ {ρ} → %V ρ → Linear %V (\ρs → %E (ρ ∷ ρs)) ε → Linear %V %E ε
    appendLinear v l = v ∷ moveLinear l
    -}

  module _ {Ω : Set} {%V : Ω → Set} where
    --anyLinear : ∀ {τs} → (g : Ω → Ω) → Any %V τs → Linear %V (\ρs → Any (\τ → Has ρs (g τ)) τs) ε
    anyLinear : ∀ {τs} → (g : Ω → Ω) → Any (\τ → %V (g τ)) τs → Linear %V (\ρs → Any (\τ → Has ρs (g τ)) τs) ε
    anyLinear g (here x) = x ∷ pureLinear (here $0)
    anyLinear g (there any-v) = mapLinear there (anyLinear g any-v)

    allLinear : ∀ {τs} → (g : Ω → Ω) → All (\τ → %V (g τ)) τs → Linear %V (\ρs → All (\τ → Has ρs (g τ)) τs) ε
    allLinear g ε = pureLinear ε
    allLinear {τ ∷ τs} g (v ∷ all-v) = v ∷ mapLinear' (g τ ∷ ε) (\σs all-σs → Has++l σs $0 ∷ mapAll (\i → Has++r i (g τ ∷ ε)) all-σs) (allLinear g all-v)

  module _ {%F : List Type → Type → Set} {%V : Type → Set} where
    linizeIntr : ∀ {τ} → IntrF %F %V τ → Linear %V (\ρs → IntrF %F (Has ρs) τ) ε
    linizeIntr (intrArrow f)   = mapLinear intrArrow (pureLinear f)
    linizeIntr (intrSum r)     = mapLinear intrSum (anyLinear identity r)
    linizeIntr (intrProduct r) = mapLinear intrProduct (allLinear identity r)
    linizeIntr (intrNat r)     = mapLinear intrNat (singleLinear' r $0)
    linizeIntr (intrList r)    = mapLinear intrList (singleLinear' r $0)
    linizeIntr (intrTree r)    = mapLinear intrTree (singleLinear' r $0)
    linizeIntr (intrConat (ρ ,, v , f)) = mapLinear intrConat (mapLinear (_,,_ ρ) (v ∷ f ∷ pureLinear ($1 , $0)))
    linizeIntr (intrStream (ρ ,, v , f)) = mapLinear intrStream (mapLinear (_,,_ ρ) (v ∷ f ∷ pureLinear ($1 , $0)))

    --linizeElim : ∀ Γ {τ ϕ} → ElimF %V τ ϕ → Linear %V (\ρs → ElimF (Has (Γ ++ ρs)) τ ϕ) Γ
    --linizeElim Γ rule = {!!}
    linizeElim : ∀ {τ ϕ} → ElimF %V τ ϕ → Linear %V (\ρs → ElimF (Has ρs) τ ϕ) ε
    linizeElim (elimArrow vs)   = mapLinear elimArrow (allLinear identity vs)
    linizeElim (elimSum {ϕ = ϕ} f)      = mapLinear elimSum (allLinear (\τ → τ ⇒ ϕ) f)
    linizeElim (elimProduct {ϕ = ϕ} f)  = mapLinear elimProduct (anyLinear (\τ → τ ⇒ ϕ) f)
    linizeElim (elimNat value)  = mapLinear elimNat (singleLinear' value $0)
    linizeElim (elimList value) = mapLinear elimList (singleLinear' value $0)
    linizeElim (elimTree value) = mapLinear elimTree (singleLinear' value $0)
    linizeElim elimConat        = pureLinear elimConat
    linizeElim elimStream       = pureLinear elimStream

    -- elim : %V ϕ → ElimF %V ϕ τ → ExprF _ %V τ
    -- %V ϕ → Linear %V (\ρs → ElimF (Has ρs) ϕ τ) ε → Linear %V (\ρs → ExprF _ (Has ρs) τ) ε
    lem++ε : {Ω : Set} → (ωs : List Ω) → Eq ωs (ωs ++ ε)
    lem++ε ε = refl
    lem++ε (x ∷ ωs) = cong (_∷_ x) (lem++ε ωs)

    linizeExpr : ∀ {τ} → ExprF %F %V τ → Linear %V (\ρs → ExprF %F (Has ρs) τ) ε
    linizeExpr {τ} (intr rule) = apLinear (pureLinear (\τs r → intr (transport (\τs → IntrF %F (Has τs) τ) (lem++ε τs) r))) (linizeIntr rule)
    linizeExpr (elim {ϕ} value rule) = apLinear (apLinear (pureLinear \{ (σ ∷ ε) mkSinglePred τs r → elim (Has++l τs $0) (mapElimF (\i → Has++r i (ϕ ∷ ε)) r) }) (singleLinear value)) (linizeElim rule)
    --linizeExpr (intr rule) = apLinear (pureLinear (\r → intr r)) (linizeIntr rule) --mapLinear intr (linizeIntr rule)
    --linizeExpr (elim {ϕ} value rule) = apLinear (apLinear (pureLinear (\{ {σ ∷ ε} mkSinglePred {τs} r → elim (Has++l τs $0) r})) (singleLinear value)) (linizeElim rule)

  succc : {A : Set} {a : A} {as as' : List A} → (∀ {r} → Has as r → Has as' r) → (∀ {r} → Has (a ∷ as) r → Has (a ∷ as') r)
  succc f (here refl) = here refl
  succc f (there x) = there (f x)

  {-# TERMINATING #-}
  mapTermM : ∀ {Γ Δ τ} → (∀ {ϕ} → Has Γ ϕ → Has Δ ϕ) → (TermM Γ τ → TermM Δ τ)
  mapTermM f (return x) = return (f x)
  mapTermM f (set ρ expr term) = set ρ (mapExprF (\{ρs} → mapTermM (succc* f ρs)) f expr) (mapTermM (succc f) term)

  sterm : {Γ : List Type} → ∀ {ρ τ} → Has Γ ρ → Has (ρ ∷ Γ) τ → Has Γ τ
  sterm i (here refl) = i
  sterm i (there j) = j

  sterma : {Γ : List Type} → ∀ {ρ ρ' τ} → Has (ρ ∷ Γ) τ → Has (ρ ∷ ρ' ∷ Γ) τ
  sterma (here refl) = here refl
  sterma (there i) = there (there i)

  combine2 : ∀ {Γ ρ τ} → TermM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  combine2 (return x) term2 = mapTermM (sterm x) term2
  combine2 (set ρ x term1) term2 = set ρ x (combine2 term1 (mapTermM sterma term2))

  has++m : {Ω : Set} → ∀ {σs} ρs τs {τ} → Has {Ω} (ρs ++ τs) τ → Has (ρs ++ (σs ++ τs)) τ
  has++m {Ω} {σs} ε τs i = Has++l σs i
  has++m (ρ ∷ ρs) τs {τ} (here refl) = here refl
  has++m (ρ ∷ ρs) τs {τ} (there i) = there (has++m ρs τs i)

  combinez : ∀ {Γ τ} Δ → Linear (TermM Γ) (\ρs → ExprF (TermMAbs Γ) (Has ρs) τ) Δ → TermM (Δ ++ Γ) τ
  combinez {Γ} Δ (pureLinear expr) = pure (mapExprF (mapTermM \i → has++m _ Γ i) (\i → Has++r i Γ) expr)
  combinez {Γ} Δ (_∷_ {σ} term l) = combine2 (mapTermM (\i → Has++l Δ i) term) (combinez (σ ∷ Δ) l)


  seqize : ∀ {Γ τ} → ExprF (TermMAbs Γ) (TermM Γ) τ → TermM Γ τ
  seqize expr = combinez ε (linizeExpr expr)

  {-# TERMINATING #-}
  compile' : ∀ {Γ τ} → Term Γ τ → TermM Γ τ
  compile' (var x) = return x
  compile' {Γ} {τ} (wrap expr) = seqize mapCompile
    where
      mapCompile : ExprF (TermMAbs Γ) (TermM Γ) τ
      mapCompile = mapExprF compile' compile' expr

  compile : ∀ {τ} → Term ε τ → TermM ε τ
  compile term = compile' term

-- run-time representation
module _ where
  mutual
    data Value (τ : Type) : Set where
      wrap : IntrF Closure Value τ → Value τ
  
    data Closure (ρs : List Type) (τ : Type) : Set where
      _&_ : ∀ {Γ} → Env Γ → TermMAbs Γ ρs τ → Closure ρs τ

    Env : List Type → Set
    Env Γ = All Value Γ

  data CallStack : List Type → Type → Set where
    ε : ∀ {τ} → CallStack (single τ) τ
    _∷_ : ∀ {ρs σ τ} → Closure ρs σ → CallStack (single σ) τ → CallStack ρs τ

  Machine : Type → Set
  Machine τ = CallStack ε τ

  load : ∀ {τ} → TermM ε τ → Machine τ
  load term = (ε & term) ∷ ε

-- computation step
module _ where
  data Step (τ : Type) : Set where
    finish : Value τ → Step τ
    continue : Machine τ → Step τ

  data StepExpr (τ : Type) : Set where
    finishExpr : Value τ → StepExpr τ
    continueExpr : Closure ε τ → StepExpr τ

  applyClosure : ∀ {ρs τ} → Closure ρs τ → All Value ρs → Closure ε τ
  applyClosure (env & term) values = (values ++' env) & term

  --apply* : ∀ {ρs τ} → Value (ρs ⇒* τ) → All Value ρs → Closure ε τ
  --apply* {ρs} {τ} function values = (function ∷ values) & (elim (ρs ⇒* τ) τ $0 (refl , {!!}) ▸ return $0)

  apply : ∀ {ρ τ} → Value (ρ ⇒ τ) → Value ρ → Closure ε τ
  --apply function value = apply* function (value ∷ ε)
  apply {ρ} {τ} function value = (function ∷ value ∷ ε) & (elim $0 (elimArrow ($1 ∷ ε)) ▸ return $0)

  mapMaybe : ∀ {σ τ} → Value (σ ⇒ τ) → Value (#Maybe σ) → Closure ε (#Maybe τ)
  mapMaybe function value = (function ∷ value ∷ ε) & compile' (#apply (#apply #mapMaybe (var $0)) (var $1))

  elimNatClosure : ∀ {ϕ} → Value (#Maybe ϕ ⇒ ϕ) → Value (#Nat ⇒ ϕ)
  elimNatClosure step = wrap (intrArrow ((step ∷ ε) & pure (elim $0 (elimNat $1))))

  apply'' : ∀ {σ τ} → Value (σ ⇒ τ) → Closure ε σ → Closure ε τ
  apply'' {σ} {τ} function closure = (thunk ∷ function ∷ ε) &
      ( elim $0 (elimArrow ε)
      ▸ pure (elim $2 (elimArrow ($0 ∷ ε)))
      )
    where
      thunk : Value (ε ⇒* σ)
      thunk = wrap (intrArrow closure)

  &apply : {!!}
  &apply = {!!}

  buildClosure : ∀ {τs τ} → Env τs → (All (Has τs) τs → TermM τs τ) → Closure ε τ
  buildClosure = {!!}

  stepElimF : ∀ τ ϕ → Value τ → ElimF Value τ ϕ → Closure ε ϕ
  stepElimF (ρs ⇒* τ) .τ (wrap (intrArrow closure)) (elimArrow values) = applyClosure closure values
  stepElimF (#Sum τs) ϕ (wrap (intrSum any-value)) (elimSum functions) = getAllAny (\function value → apply function value) functions any-value
  stepElimF (#Product τs) ϕ (wrap (intrProduct values)) (elimProduct any-function) = getAllAny (\value function → apply function value) values any-function
  --stepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) = apply'' step (applyClosure (mapMaybe (elimNatClosure step)) (single' value))
  --stepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) = apply'' step (mapMaybe (elimNatClosure step) value)
  stepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) = buildClosure (value ∷ step ∷ ε) (\{ ($value ∷ $step ∷ ε) → {!(&compose step (&mapMaybe (&elimNat step))) ^ value!} })
  stepElimF _ ϕ value rule = {!!}

  stepElim : ∀ {Γ τ ϕ} → Env Γ → Has Γ τ → ElimM Γ τ ϕ → Closure ε ϕ
  stepElim env x rule = stepElimF _ _ (get env x) (mapElimF (\x → get env x) {_} rule)

  stepIntrF : ∀ {τ} → IntrF Closure Value τ → Value τ
  stepIntrF rule = wrap rule

  stepIntr : ∀ {Γ τ} → Env Γ → IntrM Γ τ → Value τ
  stepIntr env rule = stepIntrF (mapIntrF (\term → env & term) (\x → get env x) {_} rule)

  stepExprM : ∀ {Γ τ} → Env Γ → ExprM Γ τ → Step τ
  stepExprM env (intr rule) = finish (stepIntr env rule)
  stepExprM env (elim x rule) = continue (stepElim env x rule ∷ ε)

  composeValueClosure : ∀ {σ τ} → Value σ → Closure (single σ) τ → Closure ε τ
  composeValueClosure value (env & term) = ((value ∷ env) & term)

  composeStackStack : ∀ {ρs σ τ} → CallStack ρs σ → CallStack (single σ) τ → CallStack ρs τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeStepStack : ∀ {σ τ} → Step σ → CallStack (single σ) τ → Step τ
  composeStepStack (finish value) ε = finish value
  composeStepStack (finish value) (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)
  composeStepStack (continue stack') stack = continue (composeStackStack stack' stack)

  stepTermM : ∀ {Γ τ} → Env Γ → TermM Γ τ → Step τ
  stepTermM env (return x) = finish (get env x)
  stepTermM env (set ρ expr term) = composeStepStack (stepExprM env expr) ((env & term) ∷ ε)

  stepClosureε : ∀ {τ} → Closure ε τ → Step τ
  stepClosureε (env & term) = stepTermM env term

  step : ∀ {τ} → Machine τ → Step τ
  step (closure ∷ stack) = composeStepStack (stepClosureε closure) stack

  step' : ∀ {τ} → Machine τ → Step τ
  step' ((env & return x) ∷ ε) = finish (get env x)
  step' ((env & return x) ∷ (env' & term) ∷ stack) = continue (((get env x ∷ env') & term) ∷ stack)
  step' ((env & (set σ (intr rule) cont)) ∷ stack) = continue (((value ∷ env) & cont) ∷ stack)
    where
      value : Value σ
      value = stepIntr env rule
  step' ((env & (set σ (elim x rule) cont)) ∷ stack) = continue ((closure ∷ (env & cont) ∷ stack))
    where
      closure : Closure ε σ
      closure = stepElim env x rule

-- run
module _ where
  Pred2 : {A : Set} → (A → Set) → (A → Set₁)
  Pred2 P a = Pred (P a)

  data AllPred {A : Set} {P : A → Set} : ∀ {as} → All₁ (\a → Pred (P a)) as → Pred (All P as) where
    ε : AllPred ε ε
    _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} {P2a : Pred (P a)} {P2as : All₁ (\a → Pred (P a)) as} → P2a Pa → AllPred P2as Pas → AllPred (P2a ∷ P2as) (Pa ∷ Pas)
  --AllPred ε ε = ⊤
  --AllPred (P2a ∷ P2as) (Pa ∷ Pas) = 

  AnyPred : {A : Set} {P : A → Set} → ∀ {as} → All₁ (\a → Pred (P a)) as → Pred (Any P as)
  AnyPred (P2a ∷ P2as) (here Pa) = P2a Pa
  AnyPred (P2a ∷ P2as) (there Pas) = AnyPred P2as Pas

  Val : Type → Set₁
  Val τ = Pred (Value τ)

  AllVal : List Type → Set₁
  AllVal τs = All₁ Val τs

  data TraceStepF {τ} (%GoodValue : Val τ) : Step τ → Set where
    goodFinish : {value : Value τ} → %GoodValue value → TraceStepF %GoodValue (finish value)
    goodContinue : {machine : Machine τ} → TraceStepF %GoodValue (step machine) → TraceStepF %GoodValue (continue machine)

  TraceClosureF : ∀ {τ} → (%Good-τ : Val τ) → Closure ε τ → Set
  --TraceClosureF {τ} %Good-τ closure = TraceStepF %Good-τ (continue (closure ∷ ε))
  TraceClosureF {τ} %Good-τ closure = TraceStepF %Good-τ (stepClosureε closure)

  -- good types
  module _ where
    AllGoodF : ∀ {τs} → All₁ Val τs → All Value τs → Set
    --AllGoodF {ε} ε ε = ⊤
    --AllGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (value ∷ values) = Good-τ value × AllGoodF Good-τs values
    AllGoodF = AllPred

    AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set
    --AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (here value) = Good-τ value
    --AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (there any-value) = AnyGoodF Good-τs any-value
    AnyGoodF = AnyPred
    --data AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set where
    --  here : ∀ {τ τs} {Good-τ : Val τ} {Good-τs : All₁ Val τs} {value} → Good-τ value → AnyGoodF (Good-τ ∷ Good-τs) (here value)
    --  there : ∀ {τ τs} {Good-τ Good-τs any-value} → AnyGoodF {τs} Good-τs any-value → AnyGoodF {τ ∷ τs} (Good-τ ∷ Good-τs) (there any-value)

    Good-⇒ : ∀ {ρs τ} → AllVal ρs → Val τ → Val (ρs ⇒* τ)
    Good-⇒ {ρs} {τ} Good-ρs Good-τ (wrap (intrArrow closure)) = {values : All Value ρs} → AllGoodF Good-ρs values → TraceClosureF Good-τ (applyClosure closure values)

    Good-Sum : ∀ {τs} → AllVal τs → Val (#Sum τs)
    Good-Sum Good-τs (wrap (intrSum any-value)) = AnyGoodF Good-τs any-value

    Good-Product : ∀ {τs} → AllVal τs → Val (#Product τs)
    Good-Product Good-τs (wrap (intrProduct values)) = AllGoodF Good-τs values

    Good-Void : Val #Void
    Good-Void = Good-Sum ε
    
    Good-Unit : Val #Unit
    Good-Unit = Good-Product ε
    
    Good-Either : ∀ {σ τ} → Val σ → Val τ → Val (#Either σ τ)
    Good-Either Good-σ Good-τ = Good-Sum (Good-σ ∷ Good-τ ∷ ε)
    
    Good-Pair : ∀ {σ τ} → Val σ → Val τ → Val (#Pair σ τ)
    --Good-Pair Good-σ Good-τ = Good-Product (Good-σ ∷ Good-τ ∷ ε)
    Good-Pair Good-σ Good-τ (wrap (intrProduct (value1 ∷ value2 ∷ ε))) = Good-σ value1 × Good-τ value2 × ⊤
    
    Good-Maybe : ∀ {τ} → Val τ → Val (#Maybe τ)
    --Good-Maybe Good-τ = Good-Sum (Good-Unit ∷ Good-τ ∷ ε)
    Good-Maybe Good-τ (wrap (intrSum (here unit))) = ⊤
    Good-Maybe Good-τ (wrap (intrSum (there (here value)))) = Good-τ value

    to-Good-Maybe : ∀ {τ} → (Good-τ : Val τ) → (value : Value (#Maybe τ)) → Good-Sum (Good-Unit ∷ Good-τ ∷ ε) value → Good-Maybe Good-τ value
    to-Good-Maybe Good-τ (wrap (intrSum (here unit))) good-c = tt
    to-Good-Maybe Good-τ (wrap (intrSum (there (here value)))) good-c = good-c

    {-
    -}
  
    data Good-Nat : Value #Nat → Set where
      --zero : Good-Nat #zero
      --succ : {n : Value #Nat} → Good-Nat n → Good-Nat (#succ n)
      mkGood-Nat : {n : Value (#Maybe #Nat)} → Good-Maybe Good-Nat n → Good-Nat (wrap (intrNat n))
  
    {-
    data Good-List {τ} (%Good-τ : Value τ → Set) : Value (#List τ) → Set where
      nil : Good-List %Good-τ #nil
      cons : {v : Value τ} {l : Value (#List τ)} → %Good-τ v → Good-List %Good-τ l → Good-List %Good-τ (#cons v l)
      -}

    {-
    module _ where
      record Good-Conat' {ρ} (step : Value (ρ ⇒ #Maybe ρ)) (value : Value ρ) : Set where
        coinductive
        --field force : TraceClosureF (Good-Maybe (Good-Conat' step)) (applyClosure step (single' value))
        field force : TraceClosureF (Good-Maybe (Good-Conat' step)) {!!}

      Good-Conat : Val #Conat
      Good-Conat (wrap (ρ ,, value , closure)) = Good-Conat' closure value
      -}

  mutual
    GoodValue : ∀ {τ} → Val τ
    GoodValue {ρs ⇒* τ} = Good-⇒ (AllGoodValue {ρs}) (GoodValue {τ})
    GoodValue {#Sum τs} = Good-Sum (AllGoodValue {τs})
    GoodValue {#Product τs} = Good-Product (AllGoodValue {τs})
    GoodValue {#Nat} = Good-Nat
    --GoodValue {#List τ} = Good-List (GoodValue {τ})
    --GoodValue {#Conat} = Good-Conat
    --GoodValue {#Stream τ} = Good-Stream (GoodValue {τ})
    GoodValue _ = {!!}

    AllGoodValue : ∀ {τs} → AllVal τs
    AllGoodValue {ε} = ε
    AllGoodValue {τ ∷ τs} = GoodValue {τ} ∷ AllGoodValue {τs}

  lem-AllGoodValue : ∀ {τs} {values : All Value τs} → AllPred AllGoodValue values → AllAll GoodValue values
  lem-AllGoodValue ε = ε
  lem-AllGoodValue (good-value ∷ good-values) = good-value ∷ lem-AllGoodValue good-values

  lem-AllGoodValue-r : ∀ {τs} {values : All Value τs} → AllAll GoodValue values → AllPred AllGoodValue values
  lem-AllGoodValue-r ε = ε
  lem-AllGoodValue-r (good-value ∷ good-values) = good-value ∷ lem-AllGoodValue-r good-values

  TraceStep : ∀ {τ} → Step τ → Set
  TraceStep = TraceStepF GoodValue

  Trace : ∀ {τ} → Machine τ → Set
  Trace machine = TraceStep (continue machine)

  record TraceMachine {τ} (machine : Machine τ) : Set where
    constructor mkTraceMachine
    field getTraceMachine : TraceStep (step machine)
  open TraceMachine public

  record TraceClosureε {τ} (closure : Closure ε τ) : Set where
    constructor mkTraceClosureε
    field getTraceClosureε : TraceStep (stepClosureε closure)
  open TraceClosureε public

  TraceTermM' : ∀ {ρs τ} → TermM ρs τ → Set
  TraceTermM' {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → TraceStep (stepTermM env term)

  GoodEnv : ∀ {Γ} → Env Γ → Set
  GoodEnv env = AllAll GoodValue env

  {-
  TraceStack : ∀ {ρs τ} → CallStack ρs τ → Set
  TraceStack {ρs} {τ} stack = {env : Env ρs} → AllAll GoodValue env → TraceStep (composeEnvStack env stack)
  -}

  --TraceClosureε : ∀ {τ} → Closure ε τ → Set
  --TraceClosureε {τ} closure = Trace (closure ∷ ε)

  TraceClosure : ∀ {ρs τ} → Closure ρs τ → Set
  TraceClosure {ρs} {τ} closure = {env : Env ρs} → AllAll GoodValue env → Trace (applyClosure closure env ∷ ε)

  --applyEnvStack : ∀ {ρs τ} → Env ρs → CallStack ρs τ → Step τ
  --applyEnvStack values ((env & term) ∷ stack) = continue (((values ++' env) & term) ∷ stack)
  --applyEnvStack (value ∷ ε) ε = finish value

  --TraceStack : ∀ {ρs τ} → CallStack ρs τ → Set
  --TraceStack {ρs} {τ} stack = {env : Env ρs} → AllAll GoodValue env → TraceStep (applyEnvStack env stack)

  TraceTermM : ∀ {ρs τ} → TermM ρs τ → Set
  TraceTermM {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → Trace ((env & term) ∷ ε)
  --TraceTermM {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → TraceStep (stepTermM env term)

  --Trace : ∀ {ρs τ} → TermM ρs τ → Set
  --Trace = TraceTermM
  data AllTraceStack' (P : ∀ {ρs τ} → Closure ρs τ → Set) : ∀ {ρs τ} → CallStack ρs τ → Set where
    ε : ∀ {τ} → AllTraceStack' P {single τ} {τ} ε
    _∷_ :
      ∀ {ρs σ τ} {closure : Closure ρs σ} {stack : CallStack (single σ) τ}
      → P closure → AllTraceStack' P stack → AllTraceStack' P (closure ∷ stack)

  {-
  data AllTraceStack : ∀ {ρs τ} → CallStack ρs τ → Set where
    ε : ∀ {τ} → AllTraceStack {single τ} {τ} ε
    _∷_ :
      ∀ {ρs σ τ} {closure : Closure ρs σ} {stack : CallStack (single σ) τ}
      → TraceClosure closure → AllTraceStack stack → AllTraceStack (closure ∷ stack)
      -}

  data GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set where
    mkGoodClosure : ∀ {Γ ρs τ} {env : Env Γ} {term : TermMAbs Γ ρs τ} → GoodEnv env → TraceTermM' term → GoodClosure (env & term)

  GoodStack : ∀ {ρs τ} → CallStack ρs τ → Set
  GoodStack = AllTraceStack' GoodClosure

  lem-composeStackStack :
    ∀ {ϕs ρ σ τ} → (stack1 : CallStack ϕs ρ) → (stack2 : CallStack (single ρ) σ) → (stack3 : CallStack (single σ) τ)
    → composeStackStack (composeStackStack stack1 stack2) stack3 ≡ composeStackStack stack1 (composeStackStack stack2 stack3)
  lem-composeStackStack ε stack2 stack3 = refl
  lem-composeStackStack (closure ∷ stack1) stack2 stack3 = cong (\s → closure ∷ s) (lem-composeStackStack stack1 stack2 stack3)

  lem-composeStepStack :
    ∀ {ρ σ τ} → (step : Step ρ) → (stack1 : CallStack (single ρ) σ) → (stack2 : CallStack (single σ) τ)
    → composeStepStack (composeStepStack step stack1) stack2 ≡ composeStepStack step (composeStackStack stack1 stack2)
  lem-composeStepStack (finish value) ε stack2 = refl
  lem-composeStepStack (finish value) (closure ∷ stack1) stack2 = refl
  lem-composeStepStack (continue machine) stack1 stack2 = cong continue (lem-composeStackStack machine stack1 stack2)

  lem-composeStep :
    ∀ {σ τ} → (stack1 : CallStack ε σ) → (stack2 : CallStack (single σ) τ)
    → composeStepStack (step stack1) stack2 ≡ step (composeStackStack stack1 stack2)
  lem-composeStep (closure ∷ stack1) stack2 = lem-composeStepStack (stepClosureε closure) stack1 stack2

  composeGoodValueGoodClosure :
    ∀ {σ τ} {value : Value σ} {closure : Closure (single σ) τ}
    → GoodValue value → GoodClosure closure → TraceClosureε (composeValueClosure value closure)
  composeGoodValueGoodClosure good-value (mkGoodClosure good-env trace-term) = mkTraceClosureε (trace-term (good-value ∷ good-env))

  composeTraceStepGoodStack :
    ∀ {σ τ} {step : Step σ} {stack : CallStack (single σ) τ}
    → TraceStep step → GoodStack stack → TraceStep (composeStepStack step stack)
  composeTraceStepGoodStack (goodFinish good-value) ε = goodFinish good-value
  composeTraceStepGoodStack (goodFinish good-value) (good-closure ∷ good-stack) = goodContinue (composeTraceStepGoodStack (getTraceClosureε (composeGoodValueGoodClosure good-value good-closure)) good-stack)
  composeTraceStepGoodStack {stack = stack} (goodContinue {stack'} trace-stack') good-stack = goodContinue (transport TraceStep (lem-composeStep stack' stack) (composeTraceStepGoodStack trace-stack' good-stack))

  AllGoodExpr : ∀ {Γ τ} → ExprM Γ τ → Set
  AllGoodExpr expr = AllExprF TraceTermM' (\_ → ⊤) expr

  lem-All-Pred : ∀ {τs} {values : All Value τs} → AllAll GoodValue values → AllPred AllGoodValue values
  lem-All-Pred ε = ε
  lem-All-Pred (good-value ∷ allAll) = good-value ∷ (lem-All-Pred allAll)

  lem-Any-Pred : ∀ {τs} {any-value : Any Value τs} → AllAny GoodValue any-value → AnyPred AllGoodValue any-value
  lem-Any-Pred (here x) = x
  lem-Any-Pred (there allAny) = lem-Any-Pred allAny

  goodStepIntrF :
    ∀ {τ} {rule : IntrF Closure Value τ}
    → AllIntrF GoodClosure GoodValue rule → GoodValue (stepIntrF rule)
  goodStepIntrF {_} {intrArrow .(_ & _)} (mkGoodClosure good-env good-term) = \good-values → good-term (lem-AllGoodValue good-values ++2 good-env)
  goodStepIntrF {_} {intrNat value} all-good-rule = mkGood-Nat (to-Good-Maybe Good-Nat value all-good-rule) 
  goodStepIntrF {_} {intrProduct values} all-good = lem-All-Pred all-good
  goodStepIntrF {_} {intrSum any-value} any-good = lem-Any-Pred any-good
  goodStepIntrF {_} {_} all-good-rule = {!!}

  goodStepIntr :
    ∀ {Γ τ} {env : Env Γ} {rule : IntrM Γ τ}
    → GoodEnv env → AllIntrF TraceTermM' (\_ → ⊤) rule → GoodValue (stepIntr env rule)
  goodStepIntr {env = env} {rule = rule} good-env all-trace = goodStepIntrF {rule = mapIntrF (\term → env & term) (\x → get env x) rule} (allMapIntrF (\term → env & term) TraceTermM' GoodClosure (\trace-term → mkGoodClosure good-env trace-term) (\x → get env x) (\_ → ⊤) GoodValue (\{τ} {x} _ → get2 good-env x) rule all-trace)

  composeValueStack : ∀ {σ τ} → Value σ → CallStack (single σ) τ → Step τ
  composeValueStack value ε = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)

  TraceStack : ∀ {σ τ} → CallStack (single σ) τ → Set
  TraceStack {σ} {τ} stack = {value : Value σ} → GoodValue value → TraceStep (composeValueStack value stack)

  composeTraceStepTraceStack : ∀ {σ τ} {step : Step σ} → {stack : CallStack (single σ) τ} → TraceStep step → TraceStack stack → TraceStep (composeStepStack step stack)
  composeTraceStepTraceStack {step = finish _} {stack = ε} (goodFinish x) trace-stack = goodFinish x
  composeTraceStepTraceStack {step = finish _} {stack = closure ∷ stack} (goodFinish good-value) trace-stack = trace-stack good-value
  composeTraceStepTraceStack {step = continue step} {stack = stack} (goodContinue trace-step) trace-stack = goodContinue (transport TraceStep (lem-composeStep step stack) (composeTraceStepTraceStack trace-step trace-stack))

  consTrace : ∀ {σ τ} {closure : Closure ε σ} → {stack : CallStack (single σ) τ} → TraceClosureε closure → TraceStack stack → Trace (closure ∷ stack)
  consTrace (mkTraceClosureε trace-step) trace-stack = goodContinue (composeTraceStepTraceStack trace-step trace-stack)

  good-apply'' : ∀ {σ τ} {f : Value (σ ⇒ τ)} {c : Closure ε σ} → GoodValue f → TraceClosureε c → TraceClosureε (apply'' f c)
  good-apply'' {f = wrap (intrArrow closure)} {c = env & term} good-f trace-c = mkTraceClosureε (consTrace trace-c (\good-value → goodContinue (consTrace (mkTraceClosureε (good-f (good-value ∷ ε))) \good-value' → goodContinue (goodFinish good-value'))))

  {-
  continueN : ∀ {τ} → ℕ → Machine τ → Step τ
  continueN n machine = continueN' n (continue machine) where
    continueN' : ℕ → ∀ {τ} → Step τ → Step τ
    continueN' zero step = step
    continueN' (succ n) step = continue {!continueN' n step!}

  stepN : ∀ {τ} → ℕ → Machine τ → Step τ
  stepN n machine = {!n!} where
    stepN' : ℕ → ∀ {τ} → Step τ → Step τ
    stepN' zero step = step
    stepN' (succ n) (finish x) = finish x
    stepN' (succ n) (continue x) = stepN' n (step x)

  goodContinueN : (n : ℕ) → ∀ {τ} {machine : Machine τ} → TraceStep (stepN n machine) → TraceStep (continueN n machine)
  goodContinueN n = {!!}
  -}

  traceMapMaybe : ∀ {σ τ} → (f : Value (σ ⇒ τ)) → (value : Value (#Maybe σ)) → Good-Maybe (\value' → TraceClosureε (stepElimF _ _ f (elimArrow (value' ∷ ε)))) value → TraceClosureε (mapMaybe f value)
  traceMapMaybe f = {!!}
  {-
  traceMapMaybe f (wrap (intrSum (here _))) good-maybe = mkTraceClosureε (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue ?)))))))))))
  traceMapMaybe f (wrap (intrSum (there (here nat)))) trace-closure = mkTraceClosureε (goodContinue (goodContinue (goodContinue (goodContinue {!!}))))
  -}

  lem-All-Pred-r : ∀ {τs} {values : All Value τs} → AllPred AllGoodValue values → AllAll GoodValue values
  lem-All-Pred-r ε = ε
  lem-All-Pred-r (good-value ∷ allAll) = good-value ∷ (lem-All-Pred-r allAll)

  lem-Any-Pred-r : ∀ {τs} {any-value : Any Value τs} → AnyPred AllGoodValue any-value → AllAny GoodValue any-value
  lem-Any-Pred-r {any-value = here x} p = here p
  lem-Any-Pred-r {any-value = there allAny} p = there (lem-Any-Pred-r {any-value = allAny} p)

  getAllAnyP :
    {A R : Set} {P Q : A → Set} {P2 : {a : A} → P a → Set} {Q2 : {a : A} → Q a → Set}
    → {as : List A}
    → (W : R → Set)
    → (f : ∀ {a} → P a → Q a → R)
    → (all-p : All P as) → (any-q : Any Q as)
    → AllAll P2 all-p → AllAny Q2 any-q
    → ({a : A} → (Pa : P a) → (Qa : Q a) → P2 Pa → Q2 Qa → W (f Pa Qa))
    → W (getAllAny f all-p any-q)
  getAllAnyP W f (Pa ∷ Pas) (here Qa) (x ∷ all-p) (here x₁) ff = ff Pa Qa x x₁
  getAllAnyP W f (Pa ∷ Pas) (there any-Q) (x ∷ all-p) (there any-q) ff = getAllAnyP W f Pas any-Q all-p any-q ff


  --apply : ∀ {ρ τ} → Value (ρ ⇒ τ) → Value ρ → Closure ε τ
  --apply {ρ} {τ} function value = (function ∷ value ∷ ε) & (elim $0 (elimArrow ($1 ∷ ε)) ▸ return $0)
  trace-apply : ∀ {ρ τ} {function : Value (ρ ⇒ τ)} {value : Value ρ} → GoodValue function → GoodValue value → TraceClosureε (apply function value)
  --trace-apply {_} {_} {?} good-function good-value = {!good-function!}
  trace-apply {function = wrap (intrArrow x)} good-function good-value =
    mkTraceClosureε (goodContinue (composeTraceStepTraceStack (good-function (good-value ∷ ε)) (\good-value' → goodContinue (goodFinish good-value'))))

  mutual
    traceElimNatClosure : ∀ {ϕ} → (step : Value (#Maybe ϕ ⇒ ϕ)) → (value : Value #Nat) → GoodValue step → Good-Nat value → TraceClosureε (stepElimF _ _ (elimNatClosure step) (elimArrow (value ∷ ε)))
    --traceElimNatClosure step value good-step good-value = goodContinue (consTrace (goodStepElimF #Nat _ value (elimNat step) good-value good-step) (\{ (good-v ∷ ε) → goodContinue (goodFinish good-v) }))
    --traceElimNatClosure step value good-step good-value = mkTraceClosureε (consTrace (goodStepElimF #Nat _ value (elimNat step) good-value good-step) (\{ (good-v ∷ ε) → goodContinue (goodFinish good-v) }))
    traceElimNatClosure step value good-step good-value = mkTraceClosureε (goodContinue (composeTraceStepGoodStack (getTraceClosureε (goodStepElimF {value = value} {elimNat step} good-value good-step) ) ((mkGoodClosure (good-value ∷ (good-step ∷ ε)) (λ good-env → goodFinish (get2 good-env $0))) ∷ ε) ))


    traceElimNatClosure' :
      ∀ {ϕ} → (step : Value (#Maybe ϕ ⇒ ϕ)) → (value : Value (#Maybe #Nat)) → GoodValue step → Good-Maybe Good-Nat value
      → Good-Maybe (\value' → TraceClosureε (stepElimF _ _ (elimNatClosure step) (elimArrow (value' ∷ ε)))) value
    traceElimNatClosure' step (wrap (intrSum (here _))) good-step good-value = tt
    traceElimNatClosure' step (wrap (intrSum (there (here nat)))) good-step good-value = traceElimNatClosure step nat good-step good-value

    goodStepElimF :
      ∀ {τ ϕ} {value : Value τ} {rule : ElimF Value τ ϕ}
      → GoodValue value → AllElimF GoodValue rule → TraceClosureε (stepElimF _ _ value rule)
    goodStepElimF {.(_ ⇒* _)} {_} {wrap (intrArrow x)} {elimArrow x₁} trace-term good-values = mkTraceClosureε (trace-term (lem-AllGoodValue-r good-values))
    goodStepElimF {.#Nat} {_} {wrap (intrNat value)} {elimNat step} (mkGood-Nat good-value) good-step = good-apply'' good-step (traceMapMaybe (elimNatClosure step) value (traceElimNatClosure' step value good-step good-value))
    goodStepElimF {.#Product _} {_} {wrap (intrProduct values)} {elimProduct any-function} good-values any-good-function =
      getAllAnyP TraceClosureε (\value function → apply function value) values any-function (lem-All-Pred-r good-values) any-good-function (\{value function good-value good-function → trace-apply good-function good-value})
      --{!lem-All-Pred-r good-values!}
    goodStepElimF {.#Sum _} {_} {wrap (intrSum any-value)} {elimSum functions} any-good-value good-functions =
      getAllAnyP TraceClosureε (\function value → apply function value) functions any-value good-functions (lem-Any-Pred-r any-good-value) (\{function value good-function good-value → trace-apply good-function good-value})
    goodStepElimF {_} {_} {_} {rule} good-env all-good-rule = {!!}
 {-
      good-apply'' {c = mapMaybe (elimNatClosure step) value} good-step
        (traceMapMaybe (elimNatClosure step) value (traceElimNatClosure' step value good-step good-value))
        -}

  goodStepElim :
    ∀ {Γ τ ϕ} {env : Env Γ}
    → GoodEnv env → (x : Has Γ τ) →  (rule : ElimM Γ τ ϕ) → TraceClosureε (stepElim env x rule)
  goodStepElim {Γ} {τ} {ϕ} {env = env} good-env x rule = goodStepElimF {τ} {ϕ} (get2 good-env x) (allMapElimF (\x → get env x) (\_ → ⊤) GoodValue (\{τ'} {x'} _ → get2 good-env x') rule (buildAllElim (\_ → tt) rule))

  traceExprM' : ∀ {Γ τ} {env : Env Γ} {expr : ExprM Γ τ} → GoodEnv env → AllGoodExpr expr → TraceStep (stepExprM env expr)
  traceExprM' {Γ} {τ} good-env (mkAllIntr all-intr) = goodFinish (goodStepIntr {Γ} {τ} good-env all-intr)
  traceExprM' good-env (mkAllElim {_} {_} {x} {rule} _ _) = goodContinue (composeTraceStepGoodStack (getTraceClosureε (goodStepElim good-env x rule)) ε)

  mutual
    allGoodIntr : ∀ {Γ τ} → (rule : IntrM Γ τ) → AllIntrF TraceTermM' (\_ → ⊤) rule
    allGoodIntr (intrArrow term)   = traceTermM' term
    allGoodIntr (intrSum rule)     = buildAllAny (\_ → tt) rule
    allGoodIntr (intrProduct rule) = buildAllAll (\_ → tt) rule
    allGoodIntr (intrNat rule)     = tt
    allGoodIntr (intrList rule)    = tt
    allGoodIntr (intrTree rule)    = tt
    allGoodIntr (intrConat rule)   = _ ,, (tt , tt)
    allGoodIntr (intrStream rule)  = _ ,, (tt , tt)

    allGoodExpr : ∀ {Γ τ} → (expr : ExprM Γ τ) → AllGoodExpr expr
    allGoodExpr (intr rule) = mkAllIntr (allGoodIntr rule)
    allGoodExpr (elim x rule) = mkAllElim tt (buildAllElim (\_ → tt) rule) 

    traceTermM' : ∀ {Γ τ} → (term : TermM Γ τ) → TraceTermM' term
    traceTermM' (return x) good-env = goodFinish (get2 good-env x)
    traceTermM' (set ρ expr term) {env} good-env = composeTraceStepGoodStack trace-stepExprM-env-expr trace-cons-env-term-ε
      where
        trace-term : TraceTermM' term
        trace-term = traceTermM' term

        all-good-expr : AllGoodExpr expr
        all-good-expr = allGoodExpr expr

        trace-stepExprM-env-expr : TraceStep (stepExprM env expr)
        trace-stepExprM-env-expr = traceExprM' good-env all-good-expr

        trace-cons-env-term-ε : GoodStack ((env & term) ∷ ε)
        trace-cons-env-term-ε = mkGoodClosure good-env trace-term ∷ ε

  {-
  mutual
    goodValue : ∀ {τ} → (value : Value τ) → GoodValue value
    goodValue = {!!}
    {-
    goodValue {ρs ⇒ τ} (wrap closure) = {!traceClosure closure!}
    goodValue {#Sum τs} value = {!!}
    goodValue {#Product τs} value = {!!}
    goodValue {#Nat} value = {!!}
    goodValue {#List τ} value = {!!}
    goodValue {#Conat} value = {!!}
    goodValue {#Stream τ} value = {!!}
    -}

    traceClosure : ∀ {ρs τ} → (closure : Closure ρs τ) → TraceClosure closure
    traceClosure (env & return x) good-env' = goodContinue (goodFinish {!!})
    traceClosure (env & set ρ (intr .ρ x) term) good-env' = goodContinue (goodContinue {!!})
    traceClosure (env & set ρ (elim τ .ρ x x₁) term) good-env' = goodContinue (goodContinue {!traceClosure (env & term)!})
    -}

  --traceStack : ∀ {ρs τ} → (stack : CallStack ρs τ) → TraceStack stack
  --traceStack stack = ?

  run : ∀ {τ} → (machine : Machine τ) → Trace machine
  run ((env & term) ∷ stack) = {!!}

  run' : ∀ {τ} → (term : TermM ε τ) → Trace ((ε & term) ∷ ε)
  run' term = goodContinue (transport TraceStep (lem _) (traceTermM' term ε))
    where
      lem2 : ∀ {ρs τ} → (stack : CallStack ρs τ) → stack ≡ composeStackStack stack ε
      lem2 ε = refl
      lem2 (closure ∷ stack) = cong (_∷_ closure) (lem2 stack)

      lem : ∀ {τ} → (step : Step τ) → step ≡ composeStepStack step ε
      lem (finish value) = refl
      lem (continue machine) = cong continue (lem2 machine)

  result : ∀ {τ} {machine : Machine τ} → Trace machine → Value τ
  result trace = resultStep trace where
    resultStep : ∀ {τ} {step : Step τ} → TraceStep step → Value τ
    resultStep (goodFinish {value} _good-value) = value
    resultStep (goodContinue trace) = resultStep trace

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))

module Test where
  num : ∀ Γ → ℕ → TermM Γ #Nat
  num Γ n =
      intr (intrProduct ε) ▸
      intr (intrSum (here $0)) ▸
      intr (intrNat $0) ▸
      go n
    where
      go : ∀ {Γ} → ℕ → TermM (#Nat ∷ Γ) #Nat
      go zero = return $0
      go (succ n) =
        intr {-(#Maybe #Nat)-} (intrSum (there (here $0))) ▸
        intr (intrNat $0) ▸
        go n
  
  add : ∀ Γ → TermM (#Nat ∷ #Nat ∷ Γ) #Nat
  add _ =
    intr (intrArrow {ρs = #Unit ∷ ε} (return $2)) ▸
    intr (intrArrow {ρs = #Nat ∷ ε} (
      intr (intrSum (there (here $0))) ▸
      pure (intr (intrNat $0))
    )) ▸
    intr (intrArrow {ρs = #Maybe #Nat ∷ ε} (
      pure (elim $0 (elimSum ($2 ∷ $1 ∷ ε)))
    )) ▸
    elim $3 (elimNat $0) ▸
    return $0
  
  -- stepn : {τ : Type} → ℕ → Machine τ → Step τ
  -- stepn zero s = continue s
  -- stepn (succ n) s with step s
  -- … | finish v = finish v
  -- … | continue s' = stepn n s'
  
  test : ℕ → ℕ → TermM ε #Nat
  test n m =
    intr (intrArrow (num _ n)) ▸
    elim $0 (elimArrow ε) ▸
    intr (intrArrow (num _ m)) ▸
    elim $0 (elimArrow ε) ▸
    intr (intrArrow {ρs = #Nat ∷ #Nat ∷ ε} (add _)) ▸
    pure (elim $0 (elimArrow ($1 ∷ $3 ∷ ε)))

  toNat : Value #Nat → ℕ
  toNat (wrap (intrNat (wrap (intrSum (here x))))) = zero
  toNat (wrap (intrNat (wrap (intrSum (there (here n)))))) = succ (toNat n)
  
  _ : {!!}
  _ = {!toNat (result (run' (test 9 5)))!}
