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

  Has : {A : Set} → List A → A → Set
  Has as a = Any (Eq a) as

  data AllAll {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → All P as → Set where
    ε : AllAll P2 ε
    _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} → P2 Pa → AllAll P2 Pas → AllAll P2 (Pa ∷ Pas)

  data All× {A B : Set} (P : A → Set) (Q : B → Set) : A × B → Set where
    _,_ : ∀ {a b} → P a → Q b → All× P Q (a , b)

  data AllAny {A : Set} {P : A → Set} (P2 : ∀ {a} → P a → Set) : ∀ {as} → Any P as → Set where
    here : ∀ {a as} {Pa : P a} → P2 Pa → AllAny P2 {a ∷ as} (here Pa)
    there : ∀ {a as} {any-Pa} → AllAny P2 {as} any-Pa → AllAny P2 {a ∷ as} (there any-Pa)

  data AllΣ {A : Set} {B : A → Set} (AllB : ∀ {a} → B a → Set) : Σ A B → Set where
    _,,_ : ∀ a {b : B a} → AllB b → AllΣ AllB (a ,, b)

  Pred : Set → Set₁
  Pred A = A → Set

  transport : {A : Set} → (P : A → Set) → ∀ {a a'} → a ≡ a' → P a → P a'
  transport P refl Pa = Pa

  cong : {A B : Set} → (f : A → B) → ∀ {a a'} → a ≡ a' → f a ≡ f a'
  cong f refl = refl

  single : ∀ {A} → A → List A
  single a = a ∷ ε

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

  $0 : ∀ {A a0 as}                      → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as}                   → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as}                → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as}             → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $4 : ∀ {A a0 a1 a2 a3 a4 as}          → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ as) a4
  $5 : ∀ {A a0 a1 a2 a3 a4 a5 as}       → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ as) a5
  $6 : ∀ {A a0 a1 a2 a3 a4 a5 a6 as}    → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ as) a6
  $7 : ∀ {A a0 a1 a2 a3 a4 a5 a6 a7 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ as) a7
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2
  $4 = there $3
  $5 = there $4
  $6 = there $5
  $7 = there $6

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

  getAllAny : {A R : Set} {P Q : A → Set} → (∀ {a} → P a → Q a → R) → (∀ {as} → All P as → Any Q as → R)
  getAllAny f (Pa ∷ Pas) (here Qa) = f Pa Qa
  getAllAny f (Pa ∷ Pas) (there any-Q) = getAllAny f Pas any-Q

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get all-p any-eq = getAllAny (\{ Pa refl → Pa }) all-p any-eq

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

-- types
module _ where
  infixr 5 _⇒_
  data Type : Set where
    _⇒_      : Type → Type → Type
    #Sum     : List Type → Type
    #Product : List Type → Type
    #Nat     : Type
    #Conat   : Type
    #Stream  : Type → Type

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

-- intr, elim
module _ where
  data IntrF (%Function : Type → Type → Set) (%Value : Type → Set) : Type → Set where
    intrArrow   : ∀ {ρ τ}  → %Function ρ τ                                   → IntrF %Function %Value (ρ ⇒ τ)
    intrSum     : ∀ {τs}   → Any %Value τs                                   → IntrF %Function %Value (#Sum τs)
    intrProduct : ∀ {τs}   → All %Value τs                                   → IntrF %Function %Value (#Product τs)
    intrNat     :            %Value (#Maybe #Nat)                            → IntrF %Function %Value  #Nat
    intrConat   :            Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Maybe ρ))  → IntrF %Function %Value  #Conat
    intrStream  : ∀ {τ}    → Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Pair τ ρ)) → IntrF %Function %Value (#Stream τ)
  
  data ElimF (%Value : Type → Set) : Type → Type → Set where
    elimArrow   : ∀ {ρ τ}  → %Value ρ                                        → ElimF %Value (ρ ⇒ τ)       τ
    elimSum     : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs                    → ElimF %Value (#Sum τs)     ϕ
    elimProduct : ∀ {τs τ} → Has τs τ                                        → ElimF %Value (#Product τs) τ
    elimNat     : ∀ {ϕ}    → %Value (#Maybe ϕ ⇒ ϕ)                           → ElimF %Value  #Nat         ϕ
    elimConat   :                                                              ElimF %Value  #Conat      (#Maybe #Conat)
    elimStream  : ∀ {τ}                                                      → ElimF %Value (#Stream τ)  (#Pair τ (#Stream τ))
  
  data ExprF (%F : Type → Type → Set) (%V : Type → Set) (τ : Type) : Set where
    intr : IntrF %F %V τ               → ExprF %F %V τ
    elim : ∀ {ϕ} → %V ϕ → ElimF %V ϕ τ → ExprF %F %V τ

module _ where
  mapIntrF :
    ∀ {%F1 %F2 %V1 %V2} → (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    → (∀ {τ} → IntrF %F1 %V1 τ → IntrF %F2 %V2 τ)
  mapIntrF %mapF %mapV (intrArrow rule)   = intrArrow   (%mapF rule)
  mapIntrF %mapF %mapV (intrSum rule)     = intrSum     (mapAny %mapV rule)
  mapIntrF %mapF %mapV (intrProduct rule) = intrProduct (mapAll %mapV rule)
  mapIntrF %mapF %mapV (intrNat rule)     = intrNat     (%mapV rule)
  mapIntrF %mapF %mapV (intrConat rule)   = intrConat   (mapΣ (map× %mapV %mapV) rule)
  mapIntrF %mapF %mapV (intrStream rule)  = intrStream  (mapΣ (map× %mapV %mapV) rule)
  
  mapElimF : ∀ {%V1 %V2} → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ ϕ} → ElimF %V1 τ ϕ → ElimF %V2 τ ϕ)
  mapElimF %mapV (elimArrow rule)   = elimArrow   (%mapV rule)
  mapElimF %mapV (elimSum rule)     = elimSum     (mapAll %mapV rule)
  mapElimF %mapV (elimProduct rule) = elimProduct  rule
  mapElimF %mapV (elimNat rule)     = elimNat     (%mapV rule)
  mapElimF %mapV  elimConat         = elimConat
  mapElimF %mapV  elimStream        = elimStream

  mapExprF :
    ∀ {%F1 %F2 %V1 %V2} → (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    → (∀ {τ} → ExprF %F1 %V1 τ → ExprF %F2 %V2 τ)
  mapExprF %mapF %mapV (intr rule)       = intr (mapIntrF %mapF %mapV rule)
  mapExprF %mapF %mapV (elim value rule) = elim (%mapV value) (mapElimF %mapV rule)

  module _ {%F : Type → Type → Set} {%V : Type → Set} (%AllF : ∀ {ρ τ} → %F ρ τ → Set) (%AllV : ∀ {τ} → %V τ → Set) where
    data AllIntrF : ∀ {τ} → IntrF %F %V τ → Set where
      mkAllIntrArrow   : ∀ {ρ τ rule} → %AllF rule                   → AllIntrF (intrArrow {%F} {%V} {ρ} {τ} rule)
      mkAllIntrSum     : ∀ {τs rule} → AllAny %AllV rule            → AllIntrF (intrSum {%F} {%V} {τs} rule)
      mkAllIntrProduct : ∀ {τs rule} → AllAll %AllV rule            → AllIntrF (intrProduct {%F} {%V} {τs} rule)
      mkAllIntrNat     : ∀ {rule} → %AllV rule                   → AllIntrF (intrNat rule)
      mkAllIntrConat   : ∀ {rule} → AllΣ (All× %AllV %AllV) rule → AllIntrF (intrConat rule)
      mkAllIntrStream  : ∀ {τ rule} → AllΣ (All× %AllV %AllV) rule → AllIntrF (intrStream {%F} {%V} {τ} rule)

  module _ {%V : Type → Set} (%AllV : ∀ {τ} → %V τ → Set) where
    AllElimF : ∀ {τ ϕ} → ElimF %V τ ϕ → Set
    AllElimF (elimArrow rule)   = %AllV rule
    AllElimF (elimSum rule)     = AllAll %AllV rule
    AllElimF (elimProduct rule) = ⊤
    AllElimF (elimNat rule)     = %AllV rule
    --AllElimF (elimList rule)    = %AllV rule
    AllElimF  elimConat         = ⊤
    AllElimF  elimStream        = ⊤

  module _
      {%F : Type → Type → Set} {%V : Type → Set}
      (%AllF : ∀ {ρ τ} → %F ρ τ → Set) (%AllV : ∀ {τ} → %V τ → Set)
    where
    data AllExprF : ∀ {τ} → ExprF %F %V τ → Set where
      mkAllIntr : ∀ {τ} {rule : IntrF %F %V τ} → AllIntrF %AllF %AllV rule → AllExprF (intr rule)
      mkAllElim : ∀ {ρ τ} {value : %V ρ} {rule : ElimF %V ρ τ} → %AllV value → AllElimF %AllV rule → AllExprF (elim value rule)

  module _
      {%F1 %F2 : Type → Type → Set}
      (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ)
      (%AllF1 : ∀ {ρ τ} → %F1 ρ τ → Set)
      (%AllF2 : ∀ {ρ τ} → %F2 ρ τ → Set)
      (%allMapF : ∀ {ρ τ} {f1 : %F1 ρ τ} → %AllF1 f1 → %AllF2 (%mapF f1))

      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ {τ} → %V1 τ → Set)
      (%AllV2 : ∀ {τ} → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 v1 → %AllV2 (%mapV v1))
    where
    allMapIntrF : ∀ {τ} → (intr1 : IntrF %F1 %V1 τ) → AllIntrF %AllF1 %AllV1 intr1 → AllIntrF %AllF2 %AllV2 (mapIntrF %mapF %mapV intr1)
    allMapIntrF _   (mkAllIntrArrow all) = mkAllIntrArrow (%allMapF all)
    allMapIntrF _     (mkAllIntrSum all) = mkAllIntrSum (allMapAny %mapV _ _ %allMapV all)
    allMapIntrF _ (mkAllIntrProduct all) = mkAllIntrProduct (allMapAll %mapV _ _ %allMapV all)
    allMapIntrF _     (mkAllIntrNat all) = mkAllIntrNat (%allMapV all)
    allMapIntrF _   (mkAllIntrConat all) = mkAllIntrConat (allMapΣ (map× %mapV %mapV) _ _ (allMap× %mapV %mapV %AllV1 %AllV2 %AllV1 %AllV2 %allMapV %allMapV) all)
    allMapIntrF _  (mkAllIntrStream all) = mkAllIntrStream (allMapΣ (map× %mapV %mapV) _ _ (allMap× %mapV %mapV %AllV1 %AllV2 %AllV1 %AllV2 %allMapV %allMapV) all)

  module _
      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ {τ} → %V1 τ → Set)
      (%AllV2 : ∀ {τ} → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 v1 → %AllV2 (%mapV v1))
    where
    allMapElimF : ∀ {τ ϕ} → (elim1 : ElimF %V1 τ ϕ) → AllElimF %AllV1 elim1 → AllElimF %AllV2 (mapElimF %mapV elim1)
    --allMapElimF (elimArrow rule)   all = allMapAll %mapV _ _ %allMapV all
    allMapElimF (elimArrow rule)   all = %allMapV all
    allMapElimF (elimSum rule)     all = allMapAll %mapV _ _ %allMapV all 
    allMapElimF (elimProduct rule) all = all
    allMapElimF (elimNat rule)     all = %allMapV all 
    --allMapElimF (elimList rule)    all = %allMapV all 
    allMapElimF  elimConat         all = all
    allMapElimF  elimStream        all = all

  module _ {%V : Type → Set} {%PredV : ∀ {τ} → %V τ → Set} (%allV : ∀ {τ} → (v : %V τ) → %PredV v) where
    buildAllElim : ∀ {τ ϕ} → (rule : ElimF %V τ ϕ) → AllElimF %PredV rule
    --buildAllElim (elimArrow rule)   = buildAllAll %allV rule
    buildAllElim (elimArrow rule)   = %allV rule
    buildAllElim (elimSum rule)     = buildAllAll %allV rule
    buildAllElim (elimProduct rule) = tt
    buildAllElim (elimNat rule)     = %allV rule
    --buildAllElim (elimList rule)    = %allV rule
    buildAllElim  elimConat         = tt
    buildAllElim  elimStream        = tt

module _ where
  mutual
    -- regular de-bruijn term
    data Term (Γ : List Type) (τ : Type) : Set where
      var  : Has Γ τ → Term Γ τ
      wrap : ExprF (TermAbs Γ) (Term Γ) τ → Term Γ τ
  
    TermAbs : List Type → (Type → Type → Set)
    TermAbs Γ ρ τ = Term (ρ ∷ Γ) τ

  {-# TERMINATING #-}
  mapTerm : ∀ {Γ Δ} → (∀ {τ} → Has Γ τ → Has Δ τ) → (∀ {τ} → Term Γ τ → Term Δ τ)
  mapTerm f (var x) = var (f x)
  mapTerm f (wrap expr) = wrap (mapExprF (\{ρ} → mapTerm (succc* f (ρ ∷ ε))) (mapTerm f) expr)

  #lambda : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  #lambda f = wrap (intr (intrArrow f))

  &apply : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  &apply f a = wrap (elim f (elimArrow a))
  
  &inl : ∀ {Γ σ τ} → Term Γ σ → Term Γ (#Either σ τ)
  &inl value = wrap (intr (intrSum (here value)))
  
  &inr : ∀ {Γ σ τ} → Term Γ τ → Term Γ (#Either σ τ)
  &inr value = wrap (intr (intrSum (there (here value))))
  
  #unit : ∀ {Γ} → Term Γ #Unit
  #unit = wrap (intr (intrProduct ε))
  
  &pair : ∀ {Γ σ τ} → Term Γ σ → Term Γ τ → Term Γ (#Pair σ τ)
  &pair value1 value2 = wrap (intr (intrProduct (value1 ∷ value2 ∷ ε)))

  &fst : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ σ
  &fst pair = wrap (elim pair (elimProduct $0))

  &snd : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ τ
  &snd pair = wrap (elim pair (elimProduct $1))

  #nothing : ∀ {Γ τ} → Term Γ (#Maybe τ)
  #nothing = &inl #unit

  &just : ∀ {Γ τ} → Term Γ τ → Term Γ (#Maybe τ)
  &just a = &inr a
  
  #zero : ∀ {Γ} → Term Γ #Nat
  #zero = wrap (intr (intrNat (&inl #unit)))
  
  &succ : ∀ {Γ} → Term Γ #Nat → Term Γ #Nat
  &succ n = wrap (intr (intrNat (&inr n)))
  
  {-
  #nil : ∀ {Γ τ} → Term Γ (#List τ)
  #nil = wrap (intr (intrList (&inl #unit)))
  
  #cons : ∀ {Γ τ} → Term Γ τ → Term Γ (#List τ) → Term Γ (#List τ)
  #cons head tail = wrap (intr (intrList (&inr (&pair head tail))))
  -}

  &either : ∀ {Γ σ τ ϕ} → Term Γ (σ ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Either σ τ) → Term Γ ϕ
  &either f s e = wrap (elim e (elimSum (f ∷ s ∷ ε)))

  &maybe : ∀ {Γ τ ϕ} → Term Γ (#Unit ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Maybe τ) → Term Γ ϕ
  &maybe n j m = wrap (elim m (elimSum (n ∷ j ∷ ε)))

  succt : ∀ {Γ ρ τ} → Term Γ τ → Term (ρ ∷ Γ) τ
  succt term = mapTerm there term

  ↑_ : ∀ {Γ ρ τ} → Term Γ τ → Term (ρ ∷ Γ) τ
  ↑_ = succt

  &foldNat : ∀ {Γ ϕ} → Term Γ ϕ → Term Γ (ϕ ⇒ ϕ) → Term Γ #Nat → Term Γ ϕ
  &foldNat z s n = wrap (elim n (elimNat (#lambda (&maybe (#lambda (↑ ↑ z)) (↑ s) (var $0)))))

  &foldNat' : ∀ {Γ ϕ} → Term Γ (#Maybe ϕ ⇒ ϕ) → Term Γ #Nat → Term Γ ϕ
  &foldNat' st n = wrap (elim n (elimNat st))

  #mapMaybe : ∀ {Γ σ τ} → Term Γ ((σ ⇒ τ) ⇒ (#Maybe σ ⇒ #Maybe τ))
  #mapMaybe = #lambda (#lambda (&maybe (#lambda #nothing) (#lambda (&just (&apply (var $2) (var $0)))) (var $0)))

  &elimNat : ∀ {Γ ϕ} → Term Γ (#Maybe ϕ ⇒ ϕ) → Term Γ (#Nat ⇒ ϕ)
  &elimNat f = #lambda (&foldNat' (↑ f) (var $0))

  {-
  &foldList : ∀ {Γ τ ϕ} → Term Γ (#Maybe (#Pair τ ϕ) ⇒ ϕ) → Term Γ (#List τ) → Term Γ ϕ
  &foldList st n = wrap (elim n (elimList st))

  &elimList : ∀ {Γ τ ϕ} → Term Γ (#Maybe (#Pair τ ϕ) ⇒ ϕ) → Term Γ (#List τ ⇒ ϕ)
  &elimList f = #lambda (&foldList (↑ f) (var $0))
  -}

  #elimNat : ∀ {Γ ϕ} → Term Γ ((#Maybe ϕ ⇒ ϕ) ⇒ (#Nat ⇒ ϕ))
  #elimNat = #lambda (#lambda (&foldNat' (var $1) (var $0)))

  &mapMaybe : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe σ ⇒ #Maybe τ)
  &mapMaybe f = #lambda (&maybe (#lambda #nothing) (#lambda (&just (&apply (↑ ↑ f) (var $0)))) (var $0))

  &mapPair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Pair ρ σ ⇒ #Pair ρ τ)
  &mapPair f = #lambda (&pair (&fst (var $0)) (&apply (↑ f) (&snd (var $0))))

  &mapMaybePair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe (#Pair ρ σ) ⇒ #Maybe (#Pair ρ τ))
  &mapMaybePair f = &mapMaybe (&mapPair f)

  &compose : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (ρ ⇒ σ) → Term Γ (ρ ⇒ τ)
  &compose f g = #lambda (&apply (↑ f) (&apply (↑ g) (var $0)))

  &buildConat : ∀ {Γ ρ} → Term Γ ρ → Term Γ (ρ ⇒ #Maybe ρ) → Term Γ #Conat
  &buildConat {Γ} {ρ} v s = wrap (intr (intrConat (ρ ,, v , s)))

  &buildConatF : ∀ {Γ ρ} → Term Γ (ρ ⇒ #Maybe ρ) → Term Γ (ρ ⇒ #Conat)
  &buildConatF s = #lambda (&buildConat (var $0) (↑ s))

  &buildStream : ∀ {Γ τ ρ} → Term Γ ρ → Term Γ (ρ ⇒ #Pair τ ρ) → Term Γ (#Stream τ)
  &buildStream {Γ} {τ} {ρ} v s = wrap (intr (intrStream (ρ ,, v , s)))

  &buildStreamF : ∀ {Γ τ ρ} → Term Γ (ρ ⇒ #Pair τ ρ) → Term Γ (ρ ⇒ #Stream τ)
  &buildStreamF s = #lambda (&buildStream (var $0) (↑ s))

-- compiled representation
module _ where
  mutual
    data TermM (Γ : List Type) (τ : Type) : Set where
      return : Has Γ τ → TermM Γ τ
      set    : ∀ ρ → ExprF (AbsTermM Γ) (Has Γ) ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ

    AbsTermM : List Type → (Type → Type → Set)
    AbsTermM Γ σ τ = TermM (σ ∷ Γ) τ

  IntrM : List Type → Type → Set
  IntrM Γ τ = IntrF (AbsTermM Γ) (Has Γ) τ

  ElimM : List Type → Type → Type → Set
  ElimM Γ τ ϕ = ElimF (Has Γ) τ ϕ

  ExprM : List Type → Type → Set
  ExprM Γ τ = ExprF (AbsTermM Γ) (Has Γ) τ

  infixr 5 _▸_
  _▸_ : ∀ {Γ ρ τ} → ExprM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  _▸_ = set _

  pure : ∀ {Γ τ} → ExprM Γ τ → TermM Γ τ
  pure expr = set _ expr (return $0)

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

  module _ {Ω : Set} {%V : Ω → Set} where
    anyLinear : ∀ {τs} → (g : Ω → Ω) → Any (\τ → %V (g τ)) τs → Linear %V (\ρs → Any (\τ → Has ρs (g τ)) τs) ε
    anyLinear g (here x) = x ∷ pureLinear (here $0)
    anyLinear g (there any-v) = mapLinear there (anyLinear g any-v)

    allLinear : ∀ {τs} → (g : Ω → Ω) → All (\τ → %V (g τ)) τs → Linear %V (\ρs → All (\τ → Has ρs (g τ)) τs) ε
    allLinear g ε = pureLinear ε
    allLinear {τ ∷ τs} g (v ∷ all-v) = v ∷ mapLinear' (g τ ∷ ε) (\σs all-σs → Has++l σs $0 ∷ mapAll (\i → Has++r i (g τ ∷ ε)) all-σs) (allLinear g all-v)

  module _ {%F : Type → Type → Set} {%V : Type → Set} where
    linizeIntr : ∀ {τ} → IntrF %F %V τ → Linear %V (\ρs → IntrF %F (Has ρs) τ) ε
    linizeIntr (intrArrow f)   = mapLinear intrArrow (pureLinear f)
    linizeIntr (intrSum r)     = mapLinear intrSum (anyLinear identity r)
    linizeIntr (intrProduct r) = mapLinear intrProduct (allLinear identity r)
    linizeIntr (intrNat r)     = mapLinear intrNat (singleLinear' r $0)
    --linizeIntr (intrList r)    = mapLinear intrList (singleLinear' r $0)
    linizeIntr (intrConat (ρ ,, v , f)) = mapLinear intrConat (mapLinear (_,,_ ρ) (v ∷ f ∷ pureLinear ($1 , $0)))
    linizeIntr (intrStream (ρ ,, v , f)) = mapLinear intrStream (mapLinear (_,,_ ρ) (v ∷ f ∷ pureLinear ($1 , $0)))

    linizeElim : ∀ {τ ϕ} → ElimF %V τ ϕ → Linear %V (\ρs → ElimF (Has ρs) τ ϕ) ε
    --linizeElim (elimArrow vs)   = mapLinear elimArrow (allLinear identity vs)
    linizeElim (elimArrow v)   = mapLinear elimArrow (singleLinear' v $0)
    linizeElim (elimSum {ϕ = ϕ} f) = mapLinear elimSum (allLinear (\τ → τ ⇒ ϕ) f)
    linizeElim (elimProduct f)  = mapLinear elimProduct (pureLinear f)
    linizeElim (elimNat value)  = mapLinear elimNat (singleLinear' value $0)
    --linizeElim (elimList value) = mapLinear elimList (singleLinear' value $0)
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

  succc : {A : Set} {a : A} {as as' : List A} → (∀ {r} → Has as r → Has as' r) → (∀ {r} → Has (a ∷ as) r → Has (a ∷ as') r)
  succc f (here refl) = here refl
  succc f (there x) = there (f x)

  {-# TERMINATING #-}
  mapTermM : ∀ {Γ Δ τ} → (∀ {ϕ} → Has Γ ϕ → Has Δ ϕ) → (TermM Γ τ → TermM Δ τ)
  mapTermM f (return x) = return (f x)
  mapTermM f (set ρ expr term) = set ρ (mapExprF (\{ρ} → mapTermM (succc* f (ρ ∷ ε))) f expr) (mapTermM (succc f) term)

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

  combinez : ∀ {Γ τ} Δ → Linear (TermM Γ) (\ρs → ExprF (AbsTermM Γ) (Has ρs) τ) Δ → TermM (Δ ++ Γ) τ
  combinez {Γ} Δ (pureLinear expr) = pure (mapExprF (mapTermM \i → has++m _ Γ i) (\i → Has++r i Γ) expr)
  combinez {Γ} Δ (_∷_ {σ} term l) = combine2 (mapTermM (\i → Has++l Δ i) term) (combinez (σ ∷ Δ) l)


  seqize : ∀ {Γ τ} → ExprF (AbsTermM Γ) (TermM Γ) τ → TermM Γ τ
  seqize expr = combinez ε (linizeExpr expr)

  {-# TERMINATING #-}
  compile : ∀ {Γ τ} → Term Γ τ → TermM Γ τ
  compile (var x) = return x
  compile {Γ} {τ} (wrap expr) = seqize mapCompile
    where
      mapCompile : ExprF (AbsTermM Γ) (TermM Γ) τ
      mapCompile = mapExprF compile compile expr

-- run-time representation
module _ where
  mutual
    data Value (τ : Type) : Set where
      wrap : IntrF Closure Value τ → Value τ

    data Closure (ρ τ : Type) : Set where
      _&_ : ∀ {Γ} → Env Γ → TermM (ρ ∷ Γ) τ → Closure ρ τ

    Env : List Type → Set
    Env Γ = All Value Γ

  unwrapValue : ∀ {τ} → Value τ → IntrF Closure Value τ
  unwrapValue (wrap rule) = rule

  data Thunk (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → TermM Γ τ → Thunk τ

  data CallStack : Type → Type → Set where
    ε   : ∀ {τ} → CallStack τ τ
    _∷_ : ∀ {ρ σ τ} → Closure ρ σ → CallStack σ τ → CallStack ρ τ

  data Machine : Type → Set where
    _∷_ : ∀ {σ τ} → Thunk σ → CallStack σ τ → Machine τ

  composeValueClosure : ∀ {σ τ} → Value σ → Closure σ τ → Thunk τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  composeStackStack : ∀ {ρ σ τ} → CallStack ρ σ → CallStack σ τ → CallStack ρ τ
  composeStackStack ε stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  composeMachineStack : ∀ {σ τ} → Machine σ → CallStack σ τ → Machine τ
  composeMachineStack (thunk ∷ stack1) stack2 = thunk ∷ composeStackStack stack1 stack2

  load : ∀ {τ} → TermM ε τ → Machine τ
  load term = (ε & term) ∷ ε

-- computation step
module _ where
  data Step (τ : Type) : Set where
    finish   : Value τ → Step τ
    continue : Machine τ → Step τ

  composeValueStack : ∀ {σ τ} → Value σ → CallStack σ τ → Step τ
  composeValueStack value ε = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ∷ stack)

  composeStepStack : ∀ {σ τ} → Step σ → CallStack σ τ → Step τ
  composeStepStack (finish value) stack = composeValueStack value stack
  composeStepStack (continue machine) stack = continue (composeMachineStack machine stack)


  elimNatTerm : ∀ {ϕ} → TermM (#Maybe #Nat ∷ (#Maybe ϕ ⇒ ϕ) ∷ ε) ϕ
  elimNatTerm = compile (&apply (&compose $step (&mapMaybe (&elimNat $step))) $value) where
    $value = var $0
    $step = var $1

  elimNatTerm' : ∀ {ϕ} → TermM (#Maybe #Nat ∷ (#Maybe ϕ ⇒ ϕ) ∷ ε) ϕ
  elimNatTerm' =
    intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0))))) ▸
    intr (intrArrow (elim $0 (elimNat $3) ▸ pure (intr (intrSum (there (here $0)))))) ▸
    elim $2 (elimSum ($1 ∷ $0 ∷ ε)) ▸
    pure (elim $4 (elimArrow $0))

  elimConatTerm : ∀ {ρ} → TermM (ρ ∷ (ρ ⇒ #Maybe ρ) ∷ ε) (#Maybe #Conat)
  elimConatTerm = compile (&apply (&compose (&mapMaybe (&buildConatF $step)) $step) $value) where
    $value = var $0
    $step = var $1

  elimStreamTerm : ∀ {τ ρ} → TermM (ρ ∷ (ρ ⇒ #Pair τ ρ) ∷ ε) (#Pair τ (#Stream τ))
  elimStreamTerm = compile (&apply (&compose (&mapPair (&buildStreamF $step)) $step) $value) where
    $value = var $0
    $step = var $1

  applyValue : ∀ {τ ϕ} → Value (τ ⇒ ϕ) → Value τ → Thunk ϕ
  applyValue function value = (function ∷ value ∷ ε) & compile (&apply (var $0) (var $1))

  stepElimProductF : ∀ {ϕ τ} → Value τ → Eq ϕ τ → Thunk ϕ
  stepElimProductF value refl = (value ∷ ε) & return $0

  stepElimSumF : ∀ {τ ϕ} → Value (τ ⇒ ϕ) → Value τ → Thunk ϕ
  stepElimSumF function value = applyValue function value

  stepElimF : ∀ {τ ϕ} → IntrF Closure Value τ → ElimF Value τ ϕ → Thunk ϕ
  stepElimF (intrArrow closure)      (elimArrow value)   = composeValueClosure value closure
  stepElimF (intrSum any-value)      (elimSum functions) = getAllAny stepElimSumF functions any-value
  stepElimF (intrProduct values)     (elimProduct i)     = getAllAny stepElimProductF values i
  stepElimF (intrNat value)          (elimNat step)      = (value ∷ step ∷ ε) & elimNatTerm'
  stepElimF (intrConat (ρ ,, v , s))  elimConat          = (v ∷ s ∷ ε) & elimConatTerm
  stepElimF (intrStream (ρ ,, v , s)) elimStream         = (v ∷ s ∷ ε) & elimStreamTerm

  stepIntrF : ∀ {τ} → IntrF Closure Value τ → Value τ
  stepIntrF rule = wrap rule

  stepIntrM : ∀ {Γ τ} → Env Γ → IntrM Γ τ → Value τ
  stepIntrM env rule = stepIntrF (mapIntrF (\term → env & term) (\x → get env x) rule)

  stepElimM : ∀ {Γ τ ϕ} → Env Γ → Has Γ τ → ElimM Γ τ ϕ → Thunk ϕ
  stepElimM env x rule = stepElimF (unwrapValue (get env x)) (mapElimF (\x → get env x) rule)

  step : ∀ {τ} → Machine τ → Step τ
  step ((env & return x) ∷ ε) = finish (get env x)
  step ((env & return x) ∷ (env' & term) ∷ stack) = continue (((get env x ∷ env') & term) ∷ stack)
  step ((env & (set σ (intr rule) cont)) ∷ stack) = continue (((value ∷ env) & cont) ∷ stack)
    where
      value : Value σ
      value = stepIntrM env rule
  step ((env & (set σ (elim x rule) cont)) ∷ stack) = continue ((thunk ∷ (env & cont) ∷ stack))
    where
      thunk : Thunk σ
      thunk = stepElimM env x rule

-- locality lemma
module _ where
  lem-step :
      ∀ {σ τ} → (machine : Machine σ) → (stack : CallStack σ τ)
      → composeStepStack (step machine) stack ≡ step (composeMachineStack machine stack)
  lem-step ((env & return x) ∷ ε)                      ε = refl
  lem-step ((env & return x) ∷ ε)                      ((env' & term') ∷ stack) = refl
  lem-step ((env & return x) ∷ (env' & term') ∷ stack) stack' = refl
  lem-step ((env & set ρ (intr rule) term) ∷ stack)    stack' = refl
  lem-step ((env & set ρ (elim x rule) term) ∷ stack)  stack' = refl

  {-
  lem-step :
      ∀ {σ τ} → (machine : Machine σ) → (stack : CallStack σ τ)
      → step (composeMachineStack machine stack) ≡ composeStepStack (step machine) stack
  lem-step ((env & return x) ∷ ε)                      ε = refl
  lem-step ((env & return x) ∷ ε)                      ((env' & term') ∷ stack) = refl
  lem-step ((env & return x) ∷ (env' & term') ∷ stack) stack' = refl
  lem-step ((env & set ρ (intr rule) term) ∷ stack)    stack' = refl
  lem-step ((env & set ρ (elim x rule) term) ∷ stack)  stack' = refl
  -}


-- run
module _ where
  Pred2 : {A : Set} → (A → Set) → (A → Set₁)
  Pred2 P a = Pred (P a)

  data AllPred {A : Set} {P : A → Set} : ∀ {as} → All₁ (\a → Pred (P a)) as → Pred (All P as) where
    ε : AllPred ε ε
    _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} {P2a : Pred (P a)} {P2as : All₁ (\a → Pred (P a)) as} → P2a Pa → AllPred P2as Pas → AllPred (P2a ∷ P2as) (Pa ∷ Pas)

  AnyPred : {A : Set} {P : A → Set} → ∀ {as} → All₁ (\a → Pred (P a)) as → Pred (Any P as)
  AnyPred (P2a ∷ P2as) (here Pa) = P2a Pa
  AnyPred (P2a ∷ P2as) (there Pas) = AnyPred P2as Pas

  Val : Type → Set₁
  Val τ = Pred (Value τ)

  AllVal : List Type → Set₁
  AllVal τs = All₁ Val τs

  data TraceStepF {τ} (%Denotation : Val τ) : Step τ → Set where
    goodFinish : {value : Value τ} → %Denotation value → TraceStepF %Denotation (finish value)
    goodContinue : {machine : Machine τ} → TraceStepF %Denotation (step machine) → TraceStepF %Denotation (continue machine)

  TraceThunkF : ∀ {τ} → (%Good-τ : Val τ) → Thunk τ → Set
  --TraceThunkF %Good-τ thunk = TraceStepF %Good-τ (stepThunk thunk)
  TraceThunkF %Good-τ thunk = TraceStepF %Good-τ (continue (thunk ∷ ε))

  -- good types
  module _ where
    AllGoodF : ∀ {τs} → All₁ Val τs → All Value τs → Set
    AllGoodF = AllPred

    AnyGoodF : ∀ {τs} → All₁ Val τs → Any Value τs → Set
    AnyGoodF = AnyPred

    DenotationSum : ∀ {τs} → AllVal τs → Val (#Sum τs)
    DenotationSum Good-τs (wrap (intrSum any-value)) = AnyGoodF Good-τs any-value

    DenotationProduct : ∀ {τs} → AllVal τs → Val (#Product τs)
    DenotationProduct Good-τs (wrap (intrProduct values)) = AllGoodF Good-τs values

    DenotationUnit : Val #Unit
    DenotationUnit = DenotationProduct ε
    
    DenotatioinEither : ∀ {σ τ} → Val σ → Val τ → Val (#Either σ τ)
    DenotatioinEither Good-σ Good-τ = DenotationSum (Good-σ ∷ Good-τ ∷ ε)
    
    DenotationPair : ∀ {σ τ} → Val σ → Val τ → Val (#Pair σ τ)
    --Good-Pair Good-σ Good-τ = Good-Product (Good-σ ∷ Good-τ ∷ ε)
    DenotationPair Good-σ Good-τ (wrap (intrProduct (value1 ∷ value2 ∷ ε))) = Good-σ value1 × Good-τ value2 × ⊤
    
    DenotationMaybe : ∀ {τ} → Val τ → Val (#Maybe τ)
    --Good-Maybe Good-τ = Good-Sum (Good-Unit ∷ Good-τ ∷ ε)
    DenotationMaybe Good-τ (wrap (intrSum (here unit))) = ⊤
    DenotationMaybe Good-τ (wrap (intrSum (there (here value)))) = Good-τ value

    to-Good-Maybe : ∀ {τ} → (Good-τ : Val τ) → (value : Value (#Maybe τ)) → DenotationSum (DenotationUnit ∷ Good-τ ∷ ε) value → DenotationMaybe Good-τ value
    to-Good-Maybe Good-τ (wrap (intrSum (here unit))) good-c = tt
    to-Good-Maybe Good-τ (wrap (intrSum (there (here value)))) good-c = good-c

    data DenotationNat : Value #Nat → Set where
      mkGood-Nat : {n : Value (#Maybe #Nat)} → DenotationMaybe DenotationNat n → DenotationNat (wrap (intrNat n))
  
    module _ where
      record DenotationConat' {ρ} (step : Value (ρ ⇒ #Maybe ρ)) (value : Value ρ) : Set where
        coinductive
        field force : TraceThunkF (DenotationMaybe (DenotationConat' step)) (applyValue step value)

      DenotationConat : Val #Conat
      DenotationConat (wrap (intrConat (ρ ,, value , closure))) = DenotationConat' closure value

    module _ {τ} (%Good-τ : Val τ) where
      record DenotationStream' {ρ} (step : Value (ρ ⇒ #Pair τ ρ)) (value : Value ρ) : Set where
        coinductive
        field force : TraceThunkF (DenotationPair %Good-τ (DenotationStream' step)) (applyValue step value)

      DenotationStream : Val (#Stream τ)
      DenotationStream (wrap (intrStream (ρ ,, value , closure))) = DenotationStream' closure value

  DenotationArrow : ∀ {ρ τ} → Val ρ → Val τ → Val (ρ ⇒ τ)
  DenotationArrow {ρ} {τ} Good-ρ Good-τ (wrap (intrArrow closure)) = {value : Value ρ} → Good-ρ value → TraceThunkF Good-τ (composeValueClosure value closure)

  mutual
    Denotation : ∀ {τ} → Val τ
    Denotation {ρ ⇒ τ}       = DenotationArrow (Denotation {ρ}) (Denotation {τ})
    Denotation {#Sum τs}     = DenotationSum (AllDenotation {τs})
    Denotation {#Product τs} = DenotationProduct (AllDenotation {τs})
    Denotation {#Nat}        = DenotationNat
    Denotation {#Conat}      = DenotationConat
    Denotation {#Stream τ}   = DenotationStream (Denotation {τ})

    AllDenotation : ∀ {τs} → AllVal τs
    AllDenotation {ε} = ε
    AllDenotation {τ ∷ τs} = Denotation {τ} ∷ AllDenotation {τs}

  lem-AllDenotation : ∀ {τs} {values : All Value τs} → AllPred AllDenotation values → AllAll Denotation values
  lem-AllDenotation ε = ε
  lem-AllDenotation (good-value ∷ good-values) = good-value ∷ lem-AllDenotation good-values

  lem-AllDenotation-r : ∀ {τs} {values : All Value τs} → AllAll Denotation values → AllPred AllDenotation values
  lem-AllDenotation-r ε = ε
  lem-AllDenotation-r (good-value ∷ good-values) = good-value ∷ lem-AllDenotation-r good-values

  lem-Any-Pred : ∀ {τs} {any-value : Any Value τs} → AllAny Denotation any-value → AnyPred AllDenotation any-value
  lem-Any-Pred (here x) = x
  lem-Any-Pred (there allAny) = lem-Any-Pred allAny

  lem-Any-Pred-r : ∀ {τs} {any-value : Any Value τs} → AnyPred AllDenotation any-value → AllAny Denotation any-value
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


  TraceStep : ∀ {τ} → Step τ → Set
  TraceStep = TraceStepF Denotation

  --Trace : ∀ {τ} → Machine τ → Set
  --Trace machine = TraceStep (step machine)

  record TraceMachine {τ} (machine : Machine τ) : Set where
    constructor mkTraceMachine
    field getTraceMachine : TraceStep (step machine)
  open TraceMachine public

  {-
  record TraceThunk {τ} (thunk : Thunk τ) : Set where
    constructor mkTraceThunk
    --field getTraceThunk : TraceStep (stepThunk thunk)
    --field getTraceThunk : TraceStep (thunk ∷ ε)
    field getTraceThunk : TraceStep (continue (thunk ∷ ε))
  open TraceThunk public
  -}

  record TraceTermM {Γ τ} (term : TermM Γ τ) : Set where
    constructor mkTraceTermM
    --field getTraceTermM : {env : Env Γ} → AllAll Denotation env → TraceStep ((env & term) ∷ ε)
    field getTraceTermM : {env : Env Γ} → AllAll Denotation env → TraceStep (continue ((env & term) ∷ ε))
  open TraceTermM public

  TraceThunk : ∀ {τ} → Thunk τ → Set
  TraceThunk thunk = TraceStep (continue (thunk ∷ ε))

  TraceStack : ∀ {σ τ} → CallStack σ τ → Set
  TraceStack {σ} {τ} stack = {value : Value σ} → Denotation value → TraceStep (composeValueStack value stack)

  GoodEnv : ∀ {Γ} → Env Γ → Set
  GoodEnv env = AllAll Denotation env

  data GoodClosure : ∀ {ρs τ} → Closure ρs τ → Set where
    mkGoodClosure : ∀ {Γ ρ τ} {env : Env Γ} {term : TermM (ρ ∷ Γ) τ} → GoodEnv env → TraceTermM term → GoodClosure (env & term)

  composeDenotationGoodClosure :
    ∀ {σ τ} {value : Value σ} {closure : Closure σ τ}
    → Denotation value → GoodClosure closure → TraceThunk (composeValueClosure value closure)
  composeDenotationGoodClosure good-value (mkGoodClosure good-env (mkTraceTermM trace-term)) = trace-term (good-value ∷ good-env)

  goodStepIntrF :
    ∀ {τ} {rule : IntrF Closure Value τ}
    → AllIntrF GoodClosure Denotation rule → Denotation (stepIntrF rule)
  --goodStepIntrF {_} {intrArrow .(_ & _)} (mkGoodClosure good-env good-term) = \good-values → good-term (lem-AllDenotation good-values ++2 good-env)
  goodStepIntrF {_} {intrArrow .(_ & _)} (mkAllIntrArrow (mkGoodClosure good-env (mkTraceTermM good-term))) = \good-value → good-term (good-value ∷ good-env)
  goodStepIntrF {_} {intrNat value} (mkAllIntrNat all-good-rule) = mkGood-Nat (to-Good-Maybe DenotationNat value all-good-rule) 
  goodStepIntrF {_} {intrProduct values} (mkAllIntrProduct all-good) = lem-AllDenotation-r all-good
  goodStepIntrF {_} {intrSum any-value} (mkAllIntrSum any-good) = lem-Any-Pred any-good
  --goodStepIntrF {_} {intrList value} good = mkGood-List (to-Good-Maybe (Good-Pair Denotation (Good-List Denotation)) value {!!})
  goodStepIntrF {_} {_} all-good-rule = {!!}

  goodStepIntr :
    ∀ {Γ τ} {env : Env Γ} {rule : IntrM Γ τ}
    → GoodEnv env → AllIntrF TraceTermM (\_ → ⊤) rule → Denotation (stepIntrM env rule)
  goodStepIntr {env = env} {rule = rule} good-env all-trace = goodStepIntrF {rule = mapIntrF (\term → env & term) (\x → get env x) rule} (allMapIntrF (\term → env & term) TraceTermM GoodClosure (\trace-term → mkGoodClosure good-env trace-term) (\x → get env x) (\_ → ⊤) Denotation (\{τ} {x} _ → get2 good-env x) rule all-trace)

  composeTraceStepTraceStack : ∀ {σ τ} {step : Step σ} → {stack : CallStack σ τ} → TraceStep step → TraceStack stack → TraceStep (composeStepStack step stack)
  composeTraceStepTraceStack {step = finish _} {stack = ε} (goodFinish x) trace-stack = goodFinish x
  composeTraceStepTraceStack {step = finish _} {stack = closure ∷ stack} (goodFinish good-value) trace-stack = trace-stack good-value
  composeTraceStepTraceStack {step = continue step} {stack = stack} (goodContinue trace-step) trace-stack = goodContinue (transport TraceStep (lem-step step stack) (composeTraceStepTraceStack trace-step trace-stack))

  ▹ : ∀ {σ τ} {thunk : Thunk σ} → {stack : CallStack σ τ} → TraceThunk thunk → TraceStack stack → TraceStep (continue (thunk ∷ stack))
  ▹ {thunk = thunk} {stack} (goodContinue trace-step) trace-stack = goodContinue (transport TraceStep (lem-step (thunk ∷ ε) stack) (composeTraceStepTraceStack trace-step trace-stack))

  ◽_ : ∀ {τ} {value : Value τ} → Denotation value → TraceStep (finish value)
  ◽_ = goodFinish

  ∗_ : ∀ {τ} {machine : Machine τ} → TraceStep (step machine) → TraceStep (continue machine)
  ∗_ = goodContinue

  traceStepElimSumF :
    ∀ {τ ϕ} → (function : Value (τ ⇒ ϕ)) → (value : Value τ) → Denotation function → Denotation value
    → TraceThunk (stepElimSumF function value)
  traceStepElimSumF (wrap (intrArrow closure)) value good-function good-value = ∗ ▹ (good-function good-value) \good-value → ∗ ◽ good-value

  traceStepElimProductF :
    ∀ {τ ϕ} → (value : Value τ) → (eq : Eq ϕ τ) → Denotation value
    → TraceThunk (stepElimProductF value eq)
  traceStepElimProductF value refl good-value = ∗ ◽ good-value

  mutual
    traceElimNatTerm :
      ∀ {ϕ} → (step : Value (#Maybe ϕ ⇒ ϕ)) → (value : Value (#Maybe #Nat)) → Denotation step → DenotationMaybe DenotationNat value
      → TraceThunk ((value ∷ step ∷ ε) & elimNatTerm')
    traceElimNatTerm (wrap (intrArrow closure)) (wrap (intrSum (here _))) good-step good-value =
       ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ▹ (good-step ε) \good-value' →
       ∗ ◽ good-value'
    traceElimNatTerm (wrap (intrArrow closure)) (wrap (intrSum (there (here nat)))) good-step good-value =
        ∗ ∗ ∗ ∗ ∗ ▹ (goodStepElimF nat good-value (\{values} → good-step)) \good-value' →
        ∗ ∗ ∗ ∗ ▹ (good-step good-value') \good-value'' →
        ∗ ◽ good-value''

    goodStepElimF :
      ∀ {τ ϕ} (value : Value τ) {rule : ElimF Value τ ϕ}
      → Denotation value → AllElimF Denotation rule → TraceThunk (stepElimF (unwrapValue value) rule)
    goodStepElimF (wrap (intrArrow x)) {elimArrow x₁} trace-term good-value =
      --mkTraceThunk (trace-term (lem-AllDenotation-r good-values))
      trace-term good-value
    goodStepElimF (wrap (intrSum any-value)) {elimSum functions} any-good-value good-functions =
      --getAllAnyP TraceThunk (\function value → apply function value)
      getAllAnyP TraceThunk stepElimSumF
        functions any-value
        good-functions (lem-Any-Pred-r any-good-value)
        \{ function value good-function good-value → traceStepElimSumF function value good-function good-value }
    goodStepElimF (wrap (intrProduct values)) {elimProduct i} good-values t =
      getAllAnyP {Q2 = \_ → ⊤} TraceThunk stepElimProductF values i (lem-AllDenotation good-values) (buildAllAny (\_ → tt) i) \{ value refl good-value t1 → traceStepElimProductF value refl good-value } 
      --{!!}
    goodStepElimF (wrap (intrNat value)) {elimNat step} (mkGood-Nat good-value) good-step =
      traceElimNatTerm step value good-step good-value
    goodStepElimF {_} {_} (_) {rule} good-env all-good-rule =
      {!!}

  goodStepElim :
    ∀ {Γ τ ϕ} {env : Env Γ}
    → GoodEnv env → (x : Has Γ τ) →  (rule : ElimM Γ τ ϕ) → TraceThunk (stepElimM env x rule)
  goodStepElim {Γ} {τ} {ϕ} {env = env} good-env x rule = goodStepElimF {τ} {ϕ} _ (get2 good-env x) (allMapElimF (\x → get env x) (\_ → ⊤) Denotation (\{τ'} {x'} _ → get2 good-env x') rule (buildAllElim (\_ → tt) rule))

  mutual
    allGoodIntr : ∀ {Γ τ} → (rule : IntrM Γ τ) → AllIntrF TraceTermM (\_ → ⊤) rule
    allGoodIntr (intrArrow term)   = mkAllIntrArrow (mkTraceTermM (\{env} good-env → ∗ getTraceMachine (traceMachine term env ε good-env \good-value → goodFinish good-value)))
    allGoodIntr (intrSum rule)     = mkAllIntrSum (buildAllAny (\_ → tt) rule)
    allGoodIntr (intrProduct rule) = mkAllIntrProduct (buildAllAll (\_ → tt) rule)
    allGoodIntr (intrNat rule)     = mkAllIntrNat tt
    allGoodIntr (intrConat rule)   = mkAllIntrConat (_ ,, (tt , tt))
    allGoodIntr (intrStream rule)  = mkAllIntrStream (_ ,, (tt , tt))

    traceMachine : ∀ {Γ τ ϕ} → (term : TermM Γ τ) → (env : Env Γ) → (stack : CallStack τ ϕ) → GoodEnv env → TraceStack stack → TraceMachine ((env & term) ∷ stack)
    traceMachine (return x) env ε good-env trace-stack = mkTraceMachine (goodFinish (get2 good-env x))
    traceMachine (return x) env ((env' & term) ∷ stack) good-env trace-stack = mkTraceMachine (trace-stack (get2 good-env x))
    traceMachine (set ρ (intr rule) term) env stack good-env trace-stack = mkTraceMachine (goodContinue (getTraceMachine (traceMachine term (stepIntrM env rule ∷ env) stack (goodStepIntr {rule = rule} good-env (allGoodIntr rule) ∷ good-env) trace-stack)))
    traceMachine (set ρ (elim x rule) term) env stack good-env trace-stack = mkTraceMachine (▹ (goodStepElim {env = env} good-env x rule) \{value} good-value → goodContinue (getTraceMachine (traceMachine term (value ∷ env) stack (good-value ∷ good-env) trace-stack)))

  run : ∀ {τ} → (machine : Machine τ) → TraceMachine machine
  run ((env & term) ∷ stack) = {!!}

  run' : ∀ {τ} → (term : TermM ε τ) → TraceMachine ((ε & term) ∷ ε)
  run' term = traceMachine term ε ε ε goodFinish

  result : ∀ {τ} {machine : Machine τ} → TraceMachine machine → Value τ
  result (mkTraceMachine trace) = resultStep trace where
    resultStep : ∀ {τ} {step : Step τ} → TraceStep step → Value τ
    resultStep (goodFinish {value} _good-value) = value
    resultStep (goodContinue trace) = resultStep trace

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))

module Test where
  --#add : Term ε ((#Nat ∷ #Nat ∷ ε) ⇒* #Nat)
  #add : Term ε (#Nat ⇒ #Nat ⇒ #Nat)
  #add = #lambda (#lambda (&foldNat (var $1) (#lambda (&succ (var $0))) (var $0)))

  {-
  #sum : Term ε (#List #Nat ⇒ #Nat)
  #sum =
    #lambda (&foldList
      (#lambda (&maybe
        (#lambda #zero)
        --(#lambda (&apply* (↑ ↑ ↑ #add) (&fst (var $0) ∷ &snd (var $0) ∷ ε)))
        (#lambda (&apply (&apply (↑ ↑ ↑ #add) (&fst (var $0))) (&snd (var $0))))
        (var $0)
      ))
      (var $0))
      -}
  
  fromNat : ℕ → Term ε #Nat
  fromNat zero = #zero
  fromNat (succ n) = &succ (fromNat n)

  --fromList : ∀ {A τ} → (A → Term ε τ) → (List A → Term ε (#List τ))
  --fromList f ε = #nil
  --fromList f (a ∷ as) = #cons (f a) (fromList f as)
  
  toNat : Value #Nat → ℕ
  toNat (wrap (intrNat (wrap (intrSum (here x))))) = zero
  toNat (wrap (intrNat (wrap (intrSum (there (here n)))))) = succ (toNat n)

  --toList : ∀ {A τ} → (Value τ → A) → (Value (#List τ) → List A)
  --toList f (wrap (intrList (wrap (intrSum (here x))))) = ε
  --toList f (wrap (intrList (wrap (intrSum (there (here (wrap (intrProduct (t ∷ l ∷ ε))))))))) = f t ∷ toList f l

  test : ℕ → ℕ → Term ε #Nat
  test n m = &apply (&apply #add (fromNat n)) (fromNat m)

  --test' : List ℕ → Term ε #Nat
  --test' l = &apply #sum (fromList fromNat l)

  
  --_ : {!!}
  --_ = {!toNat (result (run' (compile (test 4 3))))!}
