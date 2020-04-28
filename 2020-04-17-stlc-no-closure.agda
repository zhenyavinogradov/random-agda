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

  cong : {A : Set} → (P : A → Set) → ∀ {a a'} → a ≡ a' → P a → P a'
  cong P refl Pa = Pa

  single : ∀ {A} → A → List A
  single a = a ∷ ε

  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

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
    --AllExprF (intr rule) = AllIntrF %AllF %AllV rule
    --AllExprF (elim value rule) = %AllV value × AllElimF %AllV rule

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

mutual
  -- regular de-bruijn term
  data Term (Γ : List Type) (τ : Type) : Set where
    var  : Has Γ τ → Term Γ τ
    wrap : ExprF (TermAbs Γ) (Term Γ) τ → Term Γ τ

  TermAbs : List Type → (List Type → Type → Set)
  TermAbs Γ σs τ = Term (σs ++ Γ) τ

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

  compile : ∀ {τ} → Term ε τ → TermM ε τ
  compile = {!!}

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

  pure : ∀ {Γ τ} → ExprM Γ τ → TermM Γ τ
  pure expr = set _ expr (return $0)

  --apply* : ∀ {ρs τ} → Value (ρs ⇒* τ) → All Value ρs → Closure ε τ
  --apply* {ρs} {τ} function values = (function ∷ values) & (elim (ρs ⇒* τ) τ $0 (refl , {!!}) ▸ return $0)

  apply : ∀ {ρ τ} → Value (ρ ⇒ τ) → Value ρ → Closure ε τ
  --apply function value = apply* function (value ∷ ε)
  apply {ρ} {τ} function value = (function ∷ value ∷ ε) & (elim $0 (elimArrow ($1 ∷ ε)) ▸ return $0)

  mapMaybe : ∀ {σ τ} → Value (σ ⇒ τ) → Value (#Maybe σ) → Closure ε (#Maybe τ)
  mapMaybe function value = (function ∷ value ∷ ε) &
    ( intr (intrArrow (
        intr (intrProduct ε) ▸
        pure (intr (intrSum (here $0)))
      )) ▸
      intr (intrArrow (
        elim $2 (elimArrow ($0 ∷ ε)) ▸
        pure (intr (intrSum (there (here $0))))
      )) ▸
      pure (elim $3 (elimSum ($1 ∷ $0 ∷ ε)))
    )

  elimNatClosure : ∀ {ϕ} → Value (#Maybe ϕ ⇒ ϕ) → Value (#Nat ⇒ ϕ)
  elimNatClosure step = wrap (intrArrow ((step ∷ ε) & pure (elim $0 (elimNat $1))))

  {-
  compose : ∀ {σ ρ τ} → Value (σ ⇒ τ) → Closure (single ρ) σ → Closure (single ρ) τ
  compose g f = {!g \!}

  apply' : ∀ {σ τ} → Closure (single σ) τ → Value σ → Closure ε τ
  apply' (env & term) value = (value ∷ env) & term 
  -}

  --composeClosure : ∀ {σ τ} → Value (σ ⇒ τ) → Closure ε σ → Closure ε τ
  --composeClosure = ?

  apply'' : ∀ {σ τ} → Value (σ ⇒ τ) → Closure ε σ → Closure ε τ
  apply'' {σ} {τ} function closure = (thunk ∷ function ∷ ε) &
      ( elim $0 (elimArrow ε)
      ▸ pure (elim $2 (elimArrow ($0 ∷ ε)))
      )
    where
      thunk : Value (ε ⇒* σ)
      thunk = wrap (intrArrow closure)

  stepElimF : ∀ τ ϕ → Value τ → ElimF Value τ ϕ → Closure ε ϕ
  stepElimF (ρs ⇒* τ) .τ (wrap (intrArrow closure)) (elimArrow values) = applyClosure closure values
  stepElimF (#Sum τs) ϕ (wrap (intrSum any-value)) (elimSum functions) = getAllAny (\function value → apply function value) functions any-value
  stepElimF (#Product τs) ϕ (wrap (intrProduct values)) (elimProduct any-function) = getAllAny (\value function → apply function value) values any-function
  --stepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) = apply'' step (applyClosure (mapMaybe (elimNatClosure step)) (single' value))
  stepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) = apply'' step (mapMaybe (elimNatClosure step) value)
  stepElimF _ ϕ value rule = {!!}

  stepElim : ∀ {Γ τ ϕ} → Env Γ → Has Γ τ → ElimM Γ τ ϕ → Closure ε ϕ
  stepElim env x rule = stepElimF _ _ (get env x) (mapElimF (\x → get env x) {_} rule)

  stepIntr : ∀ {Γ τ} → Env Γ → IntrM Γ τ → Value τ
  stepIntr env rule = wrap (mapIntrF (\term → env & term) (\x → get env x) {_} rule)

  stepExprM : ∀ {Γ τ} → Env Γ → ExprM Γ τ → Step τ
  stepExprM env (intr rule) = finish (stepIntr env rule)
  stepExprM env (elim x rule) = continue (stepElim env x rule ∷ ε)

  composeValueClosure : ∀ {σ τ} → Value σ → Closure (single σ) τ → Closure ε τ
  composeValueClosure value (env & term) = ((value ∷ env) & term)

  --composeValueStack : ∀ {σ τ} → Value σ → CallStack (single σ) τ → Step τ
  --composeValueStack value ε = finish value
  --composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)

  composeStackStack : ∀ {ρs σ τ} → CallStack ρs σ → CallStack (single σ) τ → CallStack ρs τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeStepStack : ∀ {σ τ} → Step σ → CallStack (single σ) τ → Step τ
  --composeStepStack (finish value) stack = composeValueStack value stack
  composeStepStack (finish value) ε = finish value
  composeStepStack (finish value) (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)
  composeStepStack (continue stack') stack = continue (composeStackStack stack' stack)

  {-
  composeStepClosure : ∀ {σ τ} → Step σ → Closure (single σ) τ → Machine τ
  composeStepClosure (finish value) closure = composeValueClosure value closure ∷ ε
  composeStepClosure (continue stack) closure = composeStackStack stack (closure ∷ ε)
  -}

  stepTermM : ∀ {Γ τ} → Env Γ → TermM Γ τ → Step τ
  stepTermM env (return x) = finish (get env x)
  --stepTermM env (set ρ expr term) = continue (composeStepClosure (stepExprM env expr) (env & term))
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
  Pred : Set → Set₁
  Pred A = A → Set

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
  TraceClosureF {τ} %Good-τ closure = TraceStepF %Good-τ (continue (closure ∷ ε))

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

    #inl : ∀ {σ τ} → Value σ → Value (#Either σ τ)
    #inl value = wrap (intrSum (here value))

    #inr : ∀ {σ τ} → Value τ → Value (#Either σ τ)
    #inr value = wrap (intrSum (there (here value)))

    #unit : Value #Unit
    #unit = wrap (intrProduct ε)

    #pair : ∀ {σ τ} → Value σ → Value τ → Value (#Pair σ τ)
    #pair value1 value2 = wrap (intrProduct (value1 ∷ value2 ∷ ε))

    #zero : Value #Nat
    #zero = wrap (intrNat (#inl #unit))
  
    #succ : Value #Nat → Value #Nat
    #succ n = wrap (intrNat (#inr n))
  
    #nil : ∀ {τ} → Value (#List τ)
    #nil = wrap (intrList (#inl #unit))
  
    #cons : ∀ {τ} → Value τ → Value (#List τ) → Value (#List τ)
    #cons head tail = wrap (intrList (#inr (#pair head tail)))
  
    data Good-Nat : Value #Nat → Set where
      --zero : Good-Nat #zero
      --succ : {n : Value #Nat} → Good-Nat n → Good-Nat (#succ n)
      mkGood-Nat : {n : Value (#Maybe #Nat)} → Good-Maybe Good-Nat n → Good-Nat (wrap (intrNat n))
  
    data Good-List {τ} (%Good-τ : Value τ → Set) : Value (#List τ) → Set where
      nil : Good-List %Good-τ #nil
      cons : {v : Value τ} {l : Value (#List τ)} → %Good-τ v → Good-List %Good-τ l → Good-List %Good-τ (#cons v l)

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

  applyEnvStack : ∀ {ρs τ} → Env ρs → CallStack ρs τ → Step τ
  applyEnvStack values ((env & term) ∷ stack) = continue (((values ++' env) & term) ∷ stack)
  applyEnvStack (value ∷ ε) ε = finish value

  TraceStack : ∀ {ρs τ} → CallStack ρs τ → Set
  TraceStack {ρs} {τ} stack = {env : Env ρs} → AllAll GoodValue env → TraceStep (applyEnvStack env stack)

  TraceTermM : ∀ {ρs τ} → TermM ρs τ → Set
  TraceTermM {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → Trace ((env & term) ∷ ε)
  --TraceTermM {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → TraceStep (stepTermM env term)

  TraceTermM' : ∀ {ρs τ} → TermM ρs τ → Set
  TraceTermM' {ρs} {τ} term = {env : Env ρs} → AllAll GoodValue env → TraceStep (stepTermM env term)

  --Trace : ∀ {ρs τ} → TermM ρs τ → Set
  --Trace = TraceTermM
  data AllTraceStack' (P : ∀ {ρs τ} → Closure ρs τ → Set) : ∀ {ρs τ} → CallStack ρs τ → Set where
    ε : ∀ {τ} → AllTraceStack' P {single τ} {τ} ε
    _∷_ :
      ∀ {ρs σ τ} {closure : Closure ρs σ} {stack : CallStack (single σ) τ}
      → P closure → AllTraceStack' P stack → AllTraceStack' P (closure ∷ stack)

  data AllTraceStack : ∀ {ρs τ} → CallStack ρs τ → Set where
    ε : ∀ {τ} → AllTraceStack {single τ} {τ} ε
    _∷_ :
      ∀ {ρs σ τ} {closure : Closure ρs σ} {stack : CallStack (single σ) τ}
      → TraceClosure closure → AllTraceStack stack → AllTraceStack (closure ∷ stack)

  data GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set where
    mkGoodClosure : ∀ {Γ ρs τ} {env : Env Γ} {term : TermMAbs Γ ρs τ} → GoodEnv env → TraceTermM' term → GoodClosure (env & term)

  GoodStack : ∀ {ρs τ} → CallStack ρs τ → Set
  GoodStack = AllTraceStack' GoodClosure

  {-
  composeGoodValueGoodStack :
    ∀ {σ τ} {value : Value σ} {stack : CallStack (single σ) τ}
    → GoodValue value → GoodStack stack → TraceStep (composeValueStack value stack)
  composeGoodValueGoodStack good-value ε = goodFinish good-value
  composeGoodValueGoodStack good-value (trace-closure ∷ all-trace-stack) = goodContinue {!!}
  -}

  {-
  composeTraceStackTraceStack :
    ∀ {ρs σ τ} {stack1 : CallStack ρs σ} {stack2 : CallStack (single σ) τ}
    → TraceStack stack1 → TraceStack stack2 → TraceStack (composeStackStack stack1 stack2)
  composeTraceStackTraceStack trace-stack1 trace-stack2 = {!trace-stack1!}

  --traceConsStack : ∀ {ρs σ τ} → {closure : Closure ε σ} → {stack : CallStack (single σ) τ} → TraceClosureε closure → TraceStack stack → Trace (closure ∷ stack)
  --traceConsStack trace-closure trace-stack = {!!}
  composeTraceStepTraceStack :
    ∀ {σ τ} {step : Step σ} {stack : CallStack (single σ) τ}
    → TraceStep step → TraceStack stack → TraceStep (composeStepStack step stack)
  composeTraceStepTraceStack (goodFinish good-value) trace-stack = {!!}
  composeTraceStepTraceStack (goodContinue trace-stack') trace-stack = goodContinue {!composeTraceStackTraceStack trace-stack' trace-stack!}

  traceGoodStack : ∀ {τ} {stack : CallStack ε τ} → GoodStack stack → TraceMachine stack
  traceGoodStack = {!!}
  -}

  {-
  consTrace' : ∀ {σ τ} {closure : Closure ε σ} → {stack : CallStack (single σ) τ} → TraceClosureε closure → TraceStack stack → TraceMachine (closure ∷ stack)
  consTrace' (mkTraceClosureε trace-step) trace-stack = mkTraceMachine (composeTraceStepTraceStack trace-step trace-stack)

  consTrace : ∀ {σ τ} {closure : Closure ε σ} → {stack : CallStack (single σ) τ} → TraceClosureε closure → TraceStack stack → Trace (closure ∷ stack)
  --consTrace (goodContinue trace-closure) trace-stack = goodContinue {!composeTraceStepTraceStack trace-closure trace-stack!}
  consTrace (mkTraceClosureε trace-step) trace-stack = goodContinue (composeTraceStepTraceStack trace-step trace-stack)
  {-
  consTrace {closure = x & return x₁} {stack = ε} (goodContinue (goodFinish x₂)) trace-stack = goodContinue (goodFinish x₂)
  consTrace {closure = x & return x₁} {stack = (x₂ & x₄) ∷ stack} (goodContinue (goodFinish x₃)) trace-stack = goodContinue (trace-stack (x₃ ∷ ε))
  consTrace {closure = x & set ρ expr x₂} {stack = stack} (goodContinue trace-closure) trace-stack = goodContinue {!consTrace!}
  -}

  allGoodValue : ∀ τ → (rule : IntrF Closure Value τ) → AllIntrF TraceClosure GoodValue rule → GoodValue (wrap rule)
  allGoodValue (σs ⇒* τ) (intrArrow closure) trace-closure = \all-good-values → trace-closure (lem-AllGoodValue all-good-values)
  allGoodValue (#Sum τs) rule all-good = {!!}
  allGoodValue (#Product τs) rule all-good = {!!}
  allGoodValue #Nat (intrNat value) good-value = mkGood-Nat (to-Good-Maybe GoodValue value good-value)
  allGoodValue _ rule all-good = {!!}
  --allGoodValue (#List τ) rule all-good = {!!}
  --allGoodValue (#Tree τ) rule all-good = {!!}
  --allGoodValue #Conat rule all-good = {!!}
  --allGoodValue (#Stream τ) rule all-good = {!!}

  goodStepIntr :
    ∀ {Γ} τ {env : Env Γ} → GoodEnv env → (rule : IntrM Γ τ) → AllIntrF TraceTermM (\_ → ⊤) rule
    → GoodValue (stepIntr env rule)
  goodStepIntr τ {env} good-env rule all-intr-good-term =
    allGoodValue τ _ (
      allMapIntrF
        (λ term → env & term) TraceTermM TraceClosure (\trace-term → \good-env' → trace-term (good-env' ++2 good-env))
        (λ x → get env x) (λ _ → ⊤) GoodValue (\{_} {x} _ → get2 good-env x)
        rule all-intr-good-term
    )

  good-apply'' : ∀ {σ τ} {f : Value (σ ⇒ τ)} {c : Closure ε σ} → GoodValue f → TraceClosureε c → TraceClosureε (apply'' f c)
  --good-apply'' {f = wrap (intrArrow closure)} {c = env & term} good-f trace-c = goodContinue (consTrace trace-c (\{ (good-v ∷ ε) → goodContinue (consTrace (good-f (good-v ∷ ε)) (\{ (good-v' ∷ ε) → goodContinue (goodFinish good-v')}))}))
  --good-apply'' {f = wrap (intrArrow closure)} {c = env & term} good-f trace-c = mkTraceClosureε (consTrace trace-c (\{ (good-v ∷ ε) → goodContinue (consTrace (good-f (good-v ∷ ε)) (\{ (good-v' ∷ ε) → goodContinue (goodFinish good-v')}))}))
  good-apply'' {f = wrap (intrArrow closure)} {c = env & term} good-f trace-c = {!!}

  traceMapMaybe : ∀ {σ τ} → (f : Value (σ ⇒ τ)) → (value : Value (#Maybe σ)) → Good-Maybe (\value' → TraceClosureε (stepElimF _ _ f (elimArrow (value' ∷ ε)))) value → TraceClosureε (mapMaybe f value)
  traceMapMaybe = {!!}
  {-
  traceMapMaybe f (wrap (intrSum (here _))) good-maybe =
    goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (goodFinish ε)))))))))
  traceMapMaybe f (wrap (intrSum (there (here nat)))) good-maybe =
    goodContinue (goodContinue (goodContinue (goodContinue (goodContinue (consTrace good-maybe (\{ (good-ss ∷ ε) →
    goodContinue (goodContinue (goodContinue (goodContinue (goodFinish good-ss))))}))))))
    -}

  mutual
    goodStepElimF : ∀ τ ϕ → (value : Value τ) → (rule : ElimF Value τ ϕ) → GoodValue value → AllElimF GoodValue rule → TraceClosureε (stepElimF τ ϕ value rule)
    goodStepElimF = {!!}
    {-
    goodStepElimF (ρs ⇒* τ) .τ (wrap (intrArrow closure)) (elimArrow values) good-closure good-values = good-closure (lem-AllGoodValue-r good-values) 
    goodStepElimF (#Sum τs) ϕ (wrap (intrSum any-value)) (elimSum functions) good-any-value good-functions = goodContinue {!!}
    goodStepElimF (#Product τs) ϕ (wrap (intrProduct values)) (elimProduct any-function) good-values good-any-function = {!!}
    goodStepElimF #Nat ϕ (wrap (intrNat value)) (elimNat step) (mkGood-Nat good-value) good-step =
      good-apply'' {c = mapMaybe (elimNatClosure step) value} good-step
        (traceMapMaybe (elimNatClosure step) value (traceElimNatClosure' step value good-step good-value))
    goodStepElimF _ = {!!}
    -}

    traceElimNatClosure' :
      ∀ {ϕ} → (step : Value (#Maybe ϕ ⇒ ϕ)) → (value : Value (#Maybe #Nat)) → _ → Good-Maybe Good-Nat value
      → Good-Maybe (\value' → TraceClosureε _) value
    traceElimNatClosure' step (wrap (intrSum (here _))) good-step good-value = tt
    traceElimNatClosure' step (wrap (intrSum (there (here nat)))) good-step good-value = traceElimNatClosure step nat good-step good-value

    traceElimNatClosure : ∀ {ϕ} → (step : Value (#Maybe ϕ ⇒ ϕ)) → (value : Value #Nat) → _ → Good-Nat value → TraceClosureε _
    --traceElimNatClosure step value good-step good-value = goodContinue (consTrace (goodStepElimF #Nat _ value (elimNat step) good-value good-step) (\{ (good-v ∷ ε) → goodContinue (goodFinish good-v) }))
    --traceElimNatClosure step value good-step good-value = mkTraceClosureε (consTrace (goodStepElimF #Nat _ value (elimNat step) good-value good-step) (\{ (good-v ∷ ε) → goodContinue (goodFinish good-v) }))
    traceElimNatClosure step value good-step good-value = {!!}

  goodStepElim : ∀ {Γ} τ ϕ {env : Env Γ} → GoodEnv env → (x : Has Γ τ) → (rule : ElimM Γ τ ϕ) → TraceClosureε (stepElim env x rule)
  goodStepElim {Γ} τ ϕ {env} good-env x rule0 = goodStepElimF _ _ value rule (get2 good-env x) all-elim-good
    where
      value : Value τ
      value = get env x

      rule : ElimF Value τ ϕ
      rule = mapElimF (get env) rule0

      all-elim-good : AllElimF GoodValue rule
      all-elim-good = allMapElimF {%V1 = Has Γ} {%V2 = Value} (\x → get env x) (\_ → ⊤) GoodValue (\{_} {x} _ → get2 good-env x) rule0 (buildAllElim (\_ → tt) rule0)

  mutual
    allIntrGoodTerm : ∀ {Γ τ} → (rule : IntrM Γ τ) → AllIntrF TraceTermM (\_ → ⊤) rule
    allIntrGoodTerm (intrArrow term)   = traceTermM term
    allIntrGoodTerm (intrSum rule)     = buildAllAny (\_ → tt) rule
    allIntrGoodTerm (intrProduct rule) = buildAllAll (\_ → tt) rule
    allIntrGoodTerm (intrNat rule)     = tt
    allIntrGoodTerm (intrList rule)    = tt
    allIntrGoodTerm (intrTree rule)    = tt
    allIntrGoodTerm (intrConat rule)   = _ ,, (tt , tt)
    allIntrGoodTerm (intrStream rule)  = _ ,, (tt , tt)

    traceTermM : ∀ {Γ τ} → (term : TermM Γ τ) → TraceTermM term
    traceTermM (return x) good-env = goodContinue (goodFinish (get2 good-env x))
    traceTermM (set τ (intr rule) term) good-env = goodContinue (traceTermM term (goodStepIntr τ good-env rule (allIntrGoodTerm rule) ∷ good-env))
    traceTermM (set ϕ (elim x rule) term) good-env = goodContinue (consTrace trace-closure \{ (good-value ∷ ε) → trace-term (good-value ∷ good-env) })
      where
        trace-closure : TraceClosureε _
        trace-closure = goodStepElim _ ϕ good-env x rule

        trace-term : TraceTermM term
        trace-term = traceTermM term

  nilTraceStack : ∀ {τ} → TraceStack {single τ} {τ} ε
  nilTraceStack = {!!}

  consTraceStack :
    ∀ {ρs σ τ} {closure : Closure ρs σ} → {stack : CallStack (single σ) τ}
    → TraceClosure closure → GoodStack stack → TraceStack (closure ∷ stack)
  consTraceStack = {!!}
  -}

  --lem-composeValueClosure : step (closure ∷ stack) ≡ composeStepStack stepClosureε stack
  --lem-composeValueClosure = ?

  lem-composeStackStack :
    ∀ {ρ σ τ} → (stack1 : CallStack ε ρ) → (stack1 : CallStack (single ρ) σ) → (stack2 : CallStack (single σ) τ)
    → composeStackStack (composeStackStack stack1 stack2) stack3 ≡ composeStackStack stack1 (composeStackStack stack2 stack3)
  lem-composeStackStack = ?

  lem-composeStepStack :
    ∀ {ρ σ τ} → (step : Step ρ) → (stack1 : CallStack (single ρ) σ) → (stack2 : CallStack (single σ) τ)
    → composeStepStack (composeStepStack step stack1) stack2 ≡ composeStepStack step (composeStackStack stack1 stack2)
  lem-composeStepStack (finish value) ε stack2 = refl
  lem-composeStepStack (finish value) (closure ∷ stack1) stack2 = refl
  lem-composeStepStack (continue machine) stack1 stack2 = {!!}

  lem-composeStackStack :
    ∀ {σ τ} → (stack1 : CallStack ε σ) → (stack2 : CallStack (single σ) τ)
    → composeStepStack (step stack1) stack2 ≡ step (composeStackStack stack1 stack2)
  lem-composeStackStack (closure ∷ stack1) stack2 = {!!}

  composeGoodValueGoodClosure :
    ∀ {σ τ} {value : Value σ} {closure : Closure (single σ) τ}
    → GoodValue value → GoodClosure closure → TraceClosureε (composeValueClosure value closure)
  composeGoodValueGoodClosure good-value (mkGoodClosure good-env trace-term) = mkTraceClosureε (trace-term (good-value ∷ good-env))

  composeTraceStepGoodStack :
    ∀ {σ τ} {step : Step σ} {stack : CallStack (single σ) τ}
    → TraceStep step → GoodStack stack → TraceStep (composeStepStack step stack)
  composeTraceStepGoodStack (goodFinish good-value) ε = goodFinish good-value
  composeTraceStepGoodStack (goodFinish good-value) (good-closure ∷ good-stack) = goodContinue (composeTraceStepGoodStack (getTraceClosureε (composeGoodValueGoodClosure good-value good-closure)) good-stack)
  composeTraceStepGoodStack {stack = stack} (goodContinue {stack'} trace-stack') good-stack = goodContinue (cong TraceStep (lem-composeStackStack stack' stack) (composeTraceStepGoodStack trace-stack' good-stack))

  traceClosureF : ∀ {Γ ρs τ} {env : Env Γ} {term : TermM (ρs ++ Γ) τ} → GoodEnv env → TraceTermM' term → TraceClosure (env & term)
  traceClosureF good-env trace-term = \good-values → {!trace-term ?!}

  AllGoodExpr : ∀ {Γ τ} → ExprM Γ τ → Set
  AllGoodExpr expr = AllExprF TraceTermM' (\_ → ⊤) expr

  traceExprM' : ∀ {Γ τ} {env : Env Γ} {expr : ExprM Γ τ} → GoodEnv env → AllGoodExpr expr → TraceStep (stepExprM env expr)
  traceExprM' good-env (mkAllIntr all-intr) = goodFinish {!!}
  traceExprM' good-env (mkAllElim _ all-expr) = goodContinue {!!}

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
        --trace-cons-env-term-ε = traceClosureF good-env trace-term ∷ ε
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
  run ((env & term) ∷ stack) = {!consTrace!}

  result : ∀ {τ} {machine : Machine τ} → Trace machine → Value τ
  result trace = resultStep trace where
    resultStep : ∀ {τ} {step : Step τ} → TraceStep step → Value τ
    resultStep (goodFinish {value} _good-value) = value
    resultStep (goodContinue trace) = resultStep trace

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))
