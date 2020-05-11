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

  data AllAll {A : Set} {P : A → Set} (P2 : (a : A) → P a → Set) : ∀ {as} → All P as → Set where
    ε : AllAll P2 ε
    _∷_ : ∀ {a as} {Pa : P a} {Pas : All P as} → P2 a Pa → AllAll P2 Pas → AllAll P2 (Pa ∷ Pas)

  data All× {A B : Set} (P : A → Set) (Q : B → Set) : A × B → Set where
    _,_ : ∀ {a b} → P a → Q b → All× P Q (a , b)

  data AllAny {A : Set} {P : A → Set} (P2 : (a : A) → P a → Set) : ∀ {as} → Any P as → Set where
    here : ∀ {a as} {Pa : P a} → P2 a Pa → AllAny P2 {a ∷ as} (here Pa)
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
  $0 = here refl
  $1 = there $0
  $2 = there $1
  $3 = there $2
  $4 = there $3

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

  zipAllAny : {A R : Set} {P Q : A → Set} → ∀ {as} → All P as → Any Q as → (∀ {a} → P a → Q a → R) → R
  zipAllAny (Pa ∷ Pas) (here Qa) f = f Pa Qa
  zipAllAny (Pa ∷ Pas) (there any-Q) f = zipAllAny Pas any-Q f

  get : ∀ {A P a as} → All {A} P as → Has as a → P a
  get all-p any-eq = zipAllAny all-p any-eq (\{ Pa refl → Pa })

  get2 : ∀ {A P a as Pas} → {P2 : ∀ (a : A) → P a → Set} → AllAll {A} {P} P2 {as} Pas → (i : Has as a) → P2 a (get Pas i)
  get2 (x ∷ x₁) (here refl) = x
  get2 (x ∷ x₁) (there i) = get2 x₁ i

  map× : {A1 B1 A2 B2 : Set} → (A1 → A2) → (B1 → B2) → A1 × B1 → A2 × B2
  map× f g (a , b) = f a , g b

  mapΣ : {A : Set} {B1 B2 : A → Set} → (∀ {a} → B1 a → B2 a) → Σ A B1 → Σ A B2
  mapΣ f (a ,, b) = (a ,, f b)

  mapAllAll :
    {A : Set} {P : A → Set} {P2 Q2 : (a : A) → P a → Set}
    → (∀ {a} → {Pa : P a} → P2 a Pa → Q2 a Pa) → ∀ {as} → {Pas : All P as} → AllAll P2 Pas → AllAll Q2 Pas
  mapAllAll f ε = ε
  mapAllAll f (P2Pa ∷ P2Pas) = f P2Pa ∷ mapAllAll f P2Pas

  buildAllAll : {A : Set} {P : A → Set} → {P2 : (a : A) → P a → Set} → (f : ∀ {a} → (Pa : P a) → P2 a Pa) → ∀ {as} → (Pas : All P as) → AllAll P2 Pas
  buildAllAll f ε = ε
  buildAllAll f (x ∷ as) = f x ∷ buildAllAll f as

  buildAllAny : {A : Set} {P : A → Set} → {P2 : (a : A) → P a → Set} → (f : ∀ {a} → (Pa : P a) → P2 a Pa) → ∀ {as} → (any-P : Any P as) → AllAny P2 any-P
  buildAllAny f (here Pa) = here (f Pa)
  buildAllAny f (there any-P) = there (buildAllAny f any-P)

  identity : {A : Set} → A → A
  identity a = a

  allMapAll : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : (a : A) → P1 a → Set) → (AllP2 : (a : A) → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 a P1a → AllP2 a (mapP P1a)) → ∀ {as} {P1as : All P1 as} → AllAll AllP1 P1as → AllAll AllP2 (mapAll mapP P1as)
  allMapAll mapP AllP1 AllP2 allMapP ε = ε
  allMapAll mapP AllP1 AllP2 allMapP (allPa ∷ allAllPas) = allMapP allPa ∷ allMapAll mapP AllP1 AllP2 allMapP allAllPas

  allMapAny : {A : Set} {P1 P2 : A → Set} → (mapP : ∀ {a} → P1 a → P2 a) → (AllP1 : (a : A) → P1 a → Set) → (AllP2 : (a : A) → P2 a → Set) → (allMapP : ∀ {a} {P1a : P1 a} → AllP1 a P1a → AllP2 a (mapP P1a)) → ∀ {as} {any-P1 : Any P1 as} → AllAny AllP1 any-P1 → AllAny AllP2 (mapAny mapP any-P1)
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
  data Intr (%Function : Type → Type → Set) (%Value : Type → Set) : Type → Set where
    intrArrow   : ∀ {ρ τ}  → %Function ρ τ                                   → Intr %Function %Value (ρ ⇒ τ)
    intrSum     : ∀ {τs}   → Any %Value τs                                   → Intr %Function %Value (#Sum τs)
    intrProduct : ∀ {τs}   → All %Value τs                                   → Intr %Function %Value (#Product τs)
    intrNat     :            %Value (#Maybe #Nat)                            → Intr %Function %Value  #Nat
    intrConat   :            Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Maybe ρ))  → Intr %Function %Value  #Conat
    intrStream  : ∀ {τ}    → Σ Type (\ρ → %Value ρ × %Value (ρ ⇒ #Pair τ ρ)) → Intr %Function %Value (#Stream τ)
  
  data Elim (%Value : Type → Set) : Type → Type → Set where
    elimArrow   : ∀ {ρ τ}  → %Value ρ                                        → Elim %Value (ρ ⇒ τ)       τ
    elimSum     : ∀ {τs ϕ} → All (\τ → %Value (τ ⇒ ϕ)) τs                    → Elim %Value (#Sum τs)     ϕ
    elimProduct : ∀ {τs τ} → Has τs τ                                        → Elim %Value (#Product τs) τ
    elimNat     : ∀ {ϕ}    → %Value (#Maybe ϕ ⇒ ϕ)                           → Elim %Value  #Nat         ϕ
    elimConat   :                                                              Elim %Value  #Conat      (#Maybe #Conat)
    elimStream  : ∀ {τ}                                                      → Elim %Value (#Stream τ)  (#Pair τ (#Stream τ))
  
  data ExprF (%F : Type → Type → Set) (%V : Type → Set) (τ : Type) : Set where
    intr : Intr %F %V τ               → ExprF %F %V τ
    elim : ∀ {ϕ} → %V ϕ → Elim %V ϕ τ → ExprF %F %V τ

module _ where
  mapIntr :
    ∀ {%F1 %F2 %V1 %V2} → (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    → (∀ {τ} → Intr %F1 %V1 τ → Intr %F2 %V2 τ)
  mapIntr %mapF %mapV (intrArrow rule)   = intrArrow   (%mapF rule)
  mapIntr %mapF %mapV (intrSum rule)     = intrSum     (mapAny %mapV rule)
  mapIntr %mapF %mapV (intrProduct rule) = intrProduct (mapAll %mapV rule)
  mapIntr %mapF %mapV (intrNat rule)     = intrNat     (%mapV rule)
  mapIntr %mapF %mapV (intrConat rule)   = intrConat   (mapΣ (map× %mapV %mapV) rule)
  mapIntr %mapF %mapV (intrStream rule)  = intrStream  (mapΣ (map× %mapV %mapV) rule)
  
  mapElim : ∀ {%V1 %V2} → (%mapV : ∀ {τ} → %V1 τ → %V2 τ) → (∀ {τ ϕ} → Elim %V1 τ ϕ → Elim %V2 τ ϕ)
  mapElim %mapV (elimArrow rule)   = elimArrow   (%mapV rule)
  mapElim %mapV (elimSum rule)     = elimSum     (mapAll %mapV rule)
  mapElim %mapV (elimProduct rule) = elimProduct  rule
  mapElim %mapV (elimNat rule)     = elimNat     (%mapV rule)
  mapElim %mapV  elimConat         = elimConat
  mapElim %mapV  elimStream        = elimStream

  mapExprF :
    ∀ {%F1 %F2 %V1 %V2} → (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    → (∀ {τ} → ExprF %F1 %V1 τ → ExprF %F2 %V2 τ)
  mapExprF %mapF %mapV (intr rule)       = intr (mapIntr %mapF %mapV rule)
  mapExprF %mapF %mapV (elim value rule) = elim (%mapV value) (mapElim %mapV rule)

  module _ {%F : Type → Type → Set} {%V : Type → Set} (%AllF : (ρ τ : Type) → %F ρ τ → Set) (%AllV : (τ : Type) → %V τ → Set) where
    data AllIntr : ∀ τ → Intr %F %V τ → Set where
      mkAllIntrArrow   : ∀ {ρ τ rule} → %AllF ρ τ rule                 → AllIntr _ (intrArrow {%F} {%V} {ρ} {τ} rule)
      mkAllIntrSum     : ∀ {τs rule} → AllAny %AllV rule           → AllIntr _ (intrSum {%F} {%V} {τs} rule)
      mkAllIntrProduct : ∀ {τs rule} → AllAll %AllV rule           → AllIntr _ (intrProduct {%F} {%V} {τs} rule)
      mkAllIntrNat     : ∀ {rule} → %AllV _ rule                → AllIntr _ (intrNat rule)
      mkAllIntrConat   : ∀ {rule} → AllΣ (All× (%AllV _) (%AllV _)) rule   → AllIntr _ (intrConat rule)
      mkAllIntrStream  : ∀ {τ rule} → AllΣ (All× (%AllV _) (%AllV _)) rule → AllIntr _ (intrStream {%F} {%V} {τ} rule)

  module _ {%V : Type → Set} (%AllV : (τ : Type) → %V τ → Set) where
    data AllElim : ∀ τ ϕ → Elim %V τ ϕ → Set where
      mkAllElimArrow   : ∀ {ρ τ rule} → %AllV _ rule                 → AllElim _ _ (elimArrow {%V} {ρ} {τ} rule)
      mkAllElimSum     : ∀ {τs ϕ rule} → AllAll (\τ → %AllV (τ ⇒ ϕ)) rule           → AllElim _ _ (elimSum {%V} {τs} {ϕ} rule)
      mkAllElimProduct : ∀ {τs τ rule}                               → AllElim _ _ (elimProduct {%V} {τs} {τ} rule)
      mkAllElimNat     : ∀ {ϕ rule} → %AllV _ rule                     → AllElim _ _ (elimNat {%V} {ϕ} rule)
      mkAllElimConat   :                                               AllElim _ _ (elimConat)
      mkAllElimStream  : ∀ {τ}                                       → AllElim _ _ (elimStream {%V} {τ})

  {-
  module _
      {%F : Type → Type → Set} {%V : Type → Set}
      (%AllF : ∀ {ρ τ} → %F ρ τ → Set) (%AllV : ∀ {τ} → %V τ → Set)
    where
    data AllExprF : ∀ {τ} → ExprF %F %V τ → Set where
      mkAllIntr : ∀ {τ} {rule : Intr %F %V τ} → AllIntr %AllF %AllV _ rule → AllExprF (intr rule)
      mkAllElim : ∀ {ρ τ} {value : %V ρ} {rule : Elim %V ρ τ} → %AllV value → AllElim %AllV _ _ rule → AllExprF (elim value rule)
      -}

  module _
      {%F1 %F2 : Type → Type → Set}
      (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ)
      (%AllF1 : ∀ ρ τ → %F1 ρ τ → Set)
      (%AllF2 : ∀ ρ τ → %F2 ρ τ → Set)
      (%allMapF : ∀ {ρ τ} {f1 : %F1 ρ τ} → %AllF1 ρ τ f1 → %AllF2 ρ τ (%mapF f1))

      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ τ → %V1 τ → Set)
      (%AllV2 : ∀ τ → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 τ v1 → %AllV2 τ (%mapV v1))
    where
    allMapIntr : ∀ {τ} → (intr1 : Intr %F1 %V1 τ) → AllIntr %AllF1 %AllV1 τ intr1 → AllIntr %AllF2 %AllV2 τ (mapIntr %mapF %mapV intr1)
    allMapIntr _   (mkAllIntrArrow all) = mkAllIntrArrow (%allMapF all)
    allMapIntr _     (mkAllIntrSum all) = mkAllIntrSum (allMapAny %mapV _ _ %allMapV all)
    allMapIntr _ (mkAllIntrProduct all) = mkAllIntrProduct (allMapAll %mapV _ _ %allMapV all)
    allMapIntr _     (mkAllIntrNat all) = mkAllIntrNat (%allMapV all)
    allMapIntr _   (mkAllIntrConat all) = mkAllIntrConat (allMapΣ (map× %mapV %mapV) _ _ (allMap× %mapV %mapV (%AllV1 _) (%AllV2 _) (%AllV1 _) (%AllV2 _) %allMapV %allMapV) all)
    allMapIntr _  (mkAllIntrStream all) = mkAllIntrStream (allMapΣ (map× %mapV %mapV) _ _ (allMap× %mapV %mapV (%AllV1 _) (%AllV2 _) (%AllV1 _) (%AllV2 _) %allMapV %allMapV) all)

  module _
      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ τ → %V1 τ → Set)
      (%AllV2 : ∀ τ → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 τ v1 → %AllV2 τ (%mapV v1))
    where
    allMapElim : ∀ {τ ϕ} → (elim1 : Elim %V1 τ ϕ) → AllElim %AllV1 τ ϕ elim1 → AllElim %AllV2 τ ϕ (mapElim %mapV elim1)
    allMapElim _ (mkAllElimArrow all) = mkAllElimArrow (%allMapV all)
    allMapElim _ (mkAllElimSum all)   = mkAllElimSum (allMapAll %mapV _ _ %allMapV all)
    allMapElim _  mkAllElimProduct    = mkAllElimProduct
    allMapElim _ (mkAllElimNat all)   = mkAllElimNat (%allMapV all)
    allMapElim _  mkAllElimConat      = mkAllElimConat
    allMapElim _  mkAllElimStream     = mkAllElimStream

  module _ {%V : Type → Set} {%PredV : ∀ τ → %V τ → Set} (%allV : ∀ {τ} → (v : %V τ) → %PredV τ v) where
    buildAllElim : ∀ {τ ϕ} → (rule : Elim %V τ ϕ) → AllElim %PredV τ ϕ rule
    buildAllElim (elimArrow rule)   = mkAllElimArrow (%allV rule)
    buildAllElim (elimSum rule)     = mkAllElimSum (buildAllAll %allV rule)
    buildAllElim (elimProduct rule) = mkAllElimProduct
    buildAllElim (elimNat rule)     = mkAllElimNat (%allV rule)
    buildAllElim  elimConat         = mkAllElimConat
    buildAllElim  elimStream        = mkAllElimStream

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

  #elimNat : ∀ {Γ ϕ} → Term Γ ((#Maybe ϕ ⇒ ϕ) ⇒ (#Nat ⇒ ϕ))
  #elimNat = #lambda (#lambda (&foldNat' (var $1) (var $0)))

  &mapMaybe : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe σ ⇒ #Maybe τ)
  &mapMaybe f = #lambda (&maybe (#lambda #nothing) (#lambda (&just (&apply (↑ ↑ f) (var $0)))) (var $0))

  &mapPair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Pair ρ σ ⇒ #Pair ρ τ)
  &mapPair f = #lambda (&pair (&fst (var $0)) (&apply (↑ f) (&snd (var $0))))

  &mapMaybePair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe (#Pair ρ σ) ⇒ #Maybe (#Pair ρ τ))
  &mapMaybePair f = &mapMaybe (&mapPair f)

  &compose : ∀ {Γ ρ σ τ} → Term Γ (ρ ⇒ σ) → Term Γ (σ ⇒ τ) → Term Γ (ρ ⇒ τ)
  &compose f g = #lambda (&apply (↑ g) (&apply (↑ f) (var $0)))

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
  infixr 5 _▸_
  mutual
    data TermM (Γ : List Type) (τ : Type) : Set where
      return : Has Γ τ → TermM Γ τ
      _▸_    : ∀ {ρ} → ExprF (AbsTermM Γ) (Has Γ) ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ

    AbsTermM : List Type → (Type → Type → Set)
    AbsTermM Γ σ τ = TermM (σ ∷ Γ) τ

  IntrM : List Type → Type → Set
  IntrM Γ τ = Intr (AbsTermM Γ) (Has Γ) τ

  ElimM : List Type → Type → Type → Set
  ElimM Γ τ ϕ = Elim (Has Γ) τ ϕ

  ExprM : List Type → Type → Set
  ExprM Γ τ = ExprF (AbsTermM Γ) (Has Γ) τ

  -- _▸_ : ∀ {Γ ρ τ} → ExprM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  -- _▸_ = set _

  pure : ∀ {Γ τ} → ExprM Γ τ → TermM Γ τ
  pure expr = expr ▸ return $0

-- compilation
module _ where
  data Linear {Ω : Set} (%V : Ω → Set) (%E : List Ω → Set) : List Ω → Set where
    pureLinear : ∀ {ρs} → %E ρs → Linear %V %E ρs
    _∷_ : ∀ {ρ ρs} → %V ρ → Linear %V %E (ρ ∷ ρs) → Linear %V %E ρs
  -- %V ρ₁, L (ρ₁ ∷ ρs)
  --        %V ρ₂, L (ρ₂ ∷ ρ₁ ∷ ρs)
  -- %V ρ₁, %V ρ₂, …, %V ρₙ, %E [ρₙ,…,ρ₁]

  module _ {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} where
    mapLinear : (∀ {τs} → %E1 τs → %E2 τs) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 τs)
    mapLinear f (pureLinear x) = pureLinear (f x)
    mapLinear f (value ∷ linear) = value ∷ mapLinear f linear

    mapLinear' : ∀ {Γ} → (∀ τs → %E1 τs → %E2 (τs ++ Γ)) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 (τs ++ Γ))
    mapLinear' f {τs} (pureLinear x) = pureLinear (f τs x)
    mapLinear' f (v ∷ l) = v ∷ mapLinear' f l

  -- %V ρ₁, …, %V ρₙ, (∀ {τs} → %E1 τs → %E2 (τs ++ ρsʳ ++ Γ))
  -- %V τ₁, …, %V τₖ, %E1 [τₖ…τ₁]
  -- → %V ρ₁, …, %V ρₙ, %V τ₁, …, %V τₖ, %E2 [τₖ…τ₁,ρₙ…ρ₁,Γ]
  module _ {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} where
    apLinear : ∀ {Γ} → Linear %V (\ρs → ∀ τs → %E1 τs → %E2 (τs ++ ρs)) Γ → Linear %V %E1 ε → Linear %V %E2 Γ
    apLinear (pureLinear f) l2 = mapLinear' f l2 
    apLinear (_∷_ {σ} v l1) l2 = v ∷ apLinear l1 l2

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
    allLinear {τ ∷ τs} g (v ∷ all-v) = v ∷ mapLinear' (\σs all-σs → Has++l σs $0 ∷ mapAll (\i → Has++r i (g τ ∷ ε)) all-σs) (allLinear g all-v)

  module _ {%F : Type → Type → Set} {%V : Type → Set} where
    linizeIntr : ∀ {τ} → Intr %F %V τ → Linear %V (\ρs → Intr %F (Has ρs) τ) ε
    linizeIntr (intrArrow f)             = pureLinear (intrArrow f)
    linizeIntr (intrSum r)               = mapLinear intrSum (anyLinear identity r)
    linizeIntr (intrProduct r)           = mapLinear intrProduct (allLinear identity r)
    linizeIntr (intrNat r)               = r ∷ pureLinear (intrNat $0)
    linizeIntr (intrConat (ρ ,, v , f))  = v ∷ f ∷ pureLinear (intrConat (ρ ,, $1 , $0))
    linizeIntr (intrStream (ρ ,, v , f)) = v ∷ f ∷ pureLinear (intrStream (ρ ,, $1 , $0))

    linizeElim : ∀ {τ ϕ} → Elim %V τ ϕ → Linear %V (\ρs → Elim (Has ρs) τ ϕ) ε
    linizeElim (elimArrow v)       = v ∷ pureLinear (elimArrow $0)
    linizeElim (elimSum {ϕ = ϕ} f) = mapLinear elimSum (allLinear (\τ → τ ⇒ ϕ) f)
    linizeElim (elimProduct f)     = pureLinear (elimProduct f)
    linizeElim (elimNat v)         = v ∷ pureLinear (elimNat $0)
    linizeElim elimConat           = pureLinear elimConat
    linizeElim elimStream          = pureLinear elimStream

    -- elim : %V ϕ → Elim %V ϕ τ → ExprF _ %V τ
    -- %V ϕ → Linear %V (\ρs → Elim (Has ρs) ϕ τ) ε → Linear %V (\ρs → ExprF _ (Has ρs) τ) ε
    lem++ε : {Ω : Set} → (ωs : List Ω) → Eq ωs (ωs ++ ε)
    lem++ε ε = refl
    lem++ε (x ∷ ωs) = cong (_∷_ x) (lem++ε ωs)

    linizeExpr : ∀ {τ} → ExprF %F %V τ → Linear %V (\ρs → ExprF %F (Has ρs) τ) ε
    linizeExpr {τ} (intr rule) = apLinear (pureLinear (\τs r → intr (transport (\τs → Intr %F (Has τs) τ) (lem++ε τs) r))) (linizeIntr rule)
    linizeExpr (elim {ϕ} value rule) = apLinear (apLinear (pureLinear \{ (σ ∷ ε) mkSinglePred τs r → elim (Has++l τs $0) (mapElim (\i → Has++r i (ϕ ∷ ε)) r) }) (singleLinear value)) (linizeElim rule)

  succc : {A : Set} {a : A} {as as' : List A} → (∀ {r} → Has as r → Has as' r) → (∀ {r} → Has (a ∷ as) r → Has (a ∷ as') r)
  succc f (here refl) = here refl
  succc f (there x) = there (f x)

  {-# TERMINATING #-}
  mapTermM : ∀ {Γ Δ τ} → (∀ {ϕ} → Has Γ ϕ → Has Δ ϕ) → (TermM Γ τ → TermM Δ τ)
  mapTermM f (return x) = return (f x)
  mapTermM f (expr ▸ term) = (mapExprF (\{ρ} → mapTermM (succc* f (ρ ∷ ε))) f expr) ▸ (mapTermM (succc f) term)

  sterm : {Γ : List Type} → ∀ {ρ τ} → Has Γ ρ → Has (ρ ∷ Γ) τ → Has Γ τ
  sterm i (here refl) = i
  sterm i (there j) = j

  sterma : {Γ : List Type} → ∀ {ρ ρ' τ} → Has (ρ ∷ Γ) τ → Has (ρ ∷ ρ' ∷ Γ) τ
  sterma (here refl) = here refl
  sterma (there i) = there (there i)

  combine2 : ∀ {Γ ρ τ} → TermM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  combine2 (return x) term2 = mapTermM (sterm x) term2
  combine2 (x ▸ term1) term2 = x ▸ (combine2 term1 (mapTermM sterma term2))

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
      construct : Intr Closure Value τ → Value τ

    data Closure (ρ τ : Type) : Set where
      _&_ : ∀ {Γ} → Env Γ → TermM (ρ ∷ Γ) τ → Closure ρ τ

    Env : List Type → Set
    Env Γ = All Value Γ

  IntrR : Type → Set
  IntrR τ = Intr Closure Value τ

  ElimR : Type → Type → Set
  ElimR τ ϕ = Elim Value τ ϕ

  unwrapValue : ∀ {τ} → Value τ → Intr Closure Value τ
  unwrapValue (construct rule) = rule

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

-- elimination
module _ where
  eliminateArrow : ∀ {ρ τ ϕ} → Elim Value (ρ ⇒ τ) ϕ → Value (ρ ⇒ τ) → Thunk ϕ
  eliminateArrow (elimArrow value) (construct (intrArrow closure)) = composeValueClosure value closure

  eliminateSum : ∀ {τs ϕ} → Elim Value (#Sum τs) ϕ → Value (#Sum τs) → Thunk ϕ
  eliminateSum (elimSum fs) (construct (intrSum v1)) = zipAllAny fs v1 (\f v → (f ∷ v ∷ ε) & compile (&apply (var $0) (var $1)))

  eliminateProduct : ∀ {τs ϕ} → Elim Value (#Product τs) ϕ → Value (#Product τs) → Thunk ϕ
  eliminateProduct (elimProduct i) (construct (intrProduct vs)) = (get vs i ∷ ε) & compile (var $0)

  -- (elim s ∘ intr) v = (s ∘ map (elim s)) v
  eliminateNat' : ∀ {ϕ} → Elim Value #Nat ϕ → Value #Nat → Thunk ϕ
  eliminateNat' (elimNat s) (construct (intrNat v)) =
    (v ∷ s ∷ ε) & compile (&apply (&compose (&mapMaybe (&elimNat (var $step))) (var $step)) (var $value))
    where
      $value = $0
      $step = $1

  eliminateConat' : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat' elimConat (construct (intrConat (ρ ,, v , s))) =
    (v ∷ s ∷ ε) & compile (&apply (&compose $step (&mapMaybe (&buildConatF $step))) $value)
    where
      $value = var $0
      $step = var $1

  eliminateStream' : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream' elimStream (construct (intrStream (ρ ,, v , s))) =
    (v ∷ s ∷ ε) & compile (&apply (&compose $step (&mapPair (&buildStreamF $step))) $value)
    where
      $value = var $0
      $step = var $1

  eliminateNat : ∀ {ϕ} → Elim Value #Nat ϕ → Value #Nat → Thunk ϕ
  eliminateNat (elimNat s) (construct (intrNat v)) =
    (v ∷ s ∷ ε) &
    ( intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
    ▸ intr (intrArrow (elim $0 (elimNat $3) ▸ pure (intr (intrSum (there (here $0))))))
    ▸ elim $2 (elimSum ($1 ∷ $0 ∷ ε))
    ▸ pure (elim $4 (elimArrow $0))
    )

  eliminateConat : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat elimConat (construct (intrConat (ρ ,, v , s))) =
    (v ∷ s ∷ ε) &
    ( elim $1 (elimArrow $0)
    ▸ intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
    ▸ intr (intrArrow (intr (intrConat (ρ ,, $0 , $4)) ▸ pure (intr (intrSum (there (here $0))))))
    ▸ pure (elim $2 (elimSum ($1 ∷ $0 ∷ ε)))
    )

  eliminateStream : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream elimStream (construct (intrStream (ρ ,, v , s))) =
    (v ∷ s ∷ ε) &
    ( elim $1 (elimArrow $0)
    ▸ elim $0 (elimProduct $0)
    ▸ elim $1 (elimProduct $1)
    ▸ intr (intrStream (ρ ,, $0 , $4))
    ▸ pure (intr (intrProduct ($2 ∷ $0 ∷ ε)))
    )

  eliminate : ∀ {τ ϕ} → Elim Value τ ϕ → Value τ → Thunk ϕ
  eliminate {ρ ⇒ τ}       = eliminateArrow
  eliminate {#Sum τs}     = eliminateSum
  eliminate {#Product τs} = eliminateProduct
  eliminate {#Nat}        = eliminateNat
  eliminate {#Conat}      = eliminateConat
  eliminate {#Stream τ}   = eliminateStream

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

  plugEnvIntr : ∀ {Γ τ} → Env Γ → Intr (AbsTermM Γ) (Has Γ) τ → Intr Closure Value τ
  plugEnvIntr env rule = mapIntr (\term → env & term) (\x → get env x) rule

  plugEnvElim : ∀ {Γ τ ϕ} → Env Γ → Elim (Has Γ) τ ϕ → Elim Value τ ϕ
  plugEnvElim env rule = mapElim (\x → get env x) rule

  reduce : ∀ {τ} → Machine τ → Step τ
  reduce ((env & return x) ∷ stack) = composeValueStack (get env x) stack
  reduce ((env & (intr rule ▸ cont)) ∷ stack) = continue (((value ∷ env) & cont) ∷ stack)
    where
      value : Value _
      value = construct (plugEnvIntr env rule)
  reduce ((env & (elim x rule ▸ cont)) ∷ stack) = continue ((thunk ∷ (env & cont) ∷ stack))
    where
      thunk : Thunk _
      thunk = eliminate (plugEnvElim env rule) (get env x)

-- locality lemma
module _ where
  lem-step :
      ∀ {σ τ} → (machine : Machine σ) → (stack : CallStack σ τ)
      → composeStepStack (reduce machine) stack ≡ reduce (composeMachineStack machine stack)
  lem-step ((env & return x) ∷ ε)                 stack' = refl
  lem-step ((env & return x) ∷ closure ∷ stack)   stack' = refl
  lem-step ((env & (intr rule ▸ term)) ∷ stack)   stack' = refl
  lem-step ((env & (elim x rule ▸ term)) ∷ stack) stack' = refl

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

  data TraceStepF {τ} (P : Value τ → Set) : Step τ → Set where
    !finish   : {value : Value τ} → P value → TraceStepF P (finish value)
    !continue : {machine : Machine τ} → TraceStepF P (reduce machine) → TraceStepF P (continue machine)

  record TraceMachineF {τ} (P : Value τ → Set) (machine : Machine τ) : Set where
    constructor mkTraceMachineF
    field getTraceMachineF : TraceStepF P (reduce machine)
  open TraceMachineF public

  TraceThunkF : ∀ {τ} → Val τ → Thunk τ → Set
  TraceThunkF P thunk = TraceMachineF P (thunk ∷ ε)

-- good types
module _ where
  DenotationArrow : ∀ {ρ τ} → Val ρ → Val τ → Val (ρ ⇒ τ)
  DenotationArrow {ρ} {τ} Good-ρ Good-τ (construct (intrArrow closure)) = {value : Value ρ} → Good-ρ value → TraceThunkF Good-τ (composeValueClosure value closure)

  DenotationSum : ∀ {τs} → AllVal τs → Val (#Sum τs)
  DenotationSum Good-τs (construct (intrSum any-value)) = AnyPred Good-τs any-value

  DenotationProduct : ∀ {τs} → AllVal τs → Val (#Product τs)
  DenotationProduct Good-τs (construct (intrProduct values)) = AllPred Good-τs values

  DenotationUnit : Val #Unit
  DenotationUnit = DenotationProduct ε
  
  DenotationPair : ∀ {σ τ} → Val σ → Val τ → Val (#Pair σ τ)
  --Good-Pair Good-σ Good-τ = Good-Product (Good-σ ∷ Good-τ ∷ ε)
  DenotationPair Good-σ Good-τ (construct (intrProduct (value1 ∷ value2 ∷ ε))) = Good-σ value1 × Good-τ value2 × ⊤
  
  DenotationMaybe : ∀ {τ} → Val τ → Val (#Maybe τ)
  --DenotationMaybe Good-τ = DenotationSum (DenotationUnit ∷ Good-τ ∷ ε)
  DenotationMaybe Good-τ (construct (intrSum (here unit))) = ⊤
  DenotationMaybe Good-τ (construct (intrSum (there (here value)))) = Good-τ value

  to-Good-Maybe : ∀ {τ} → (Good-τ : Val τ) → (value : Value (#Maybe τ)) → DenotationSum (DenotationUnit ∷ Good-τ ∷ ε) value → DenotationMaybe Good-τ value
  to-Good-Maybe Good-τ (construct (intrSum (here unit))) good-c = tt
  to-Good-Maybe Good-τ (construct (intrSum (there (here value)))) good-c = good-c

  data DenotationNat : Value #Nat → Set where
    !mkNat : ∀ {n} → DenotationMaybe DenotationNat n → DenotationNat (construct (intrNat n))

  applyValue : ∀ {τ ϕ} → Value (τ ⇒ ϕ) → Value τ → Thunk ϕ
  applyValue function value = (function ∷ value ∷ ε) & compile (&apply (var $0) (var $1))

  record DenotationConatU {ρ} (step : Value (ρ ⇒ #Maybe ρ)) (value : Value ρ) : Set where
    coinductive
    field forceConat : TraceThunkF (DenotationMaybe (DenotationConatU step)) (applyValue step value)
  open DenotationConatU public

  DenotationConat : Val #Conat
  DenotationConat (construct (intrConat (ρ ,, value , closure))) = DenotationConatU closure value

  record DenotationStreamU {τ ρ} (%Denotation-τ : Val τ) (step : Value (ρ ⇒ #Pair τ ρ)) (value : Value ρ) : Set where
    coinductive
    field forceStream : TraceThunkF (DenotationPair %Denotation-τ (DenotationStreamU %Denotation-τ step)) (applyValue step value)
  open DenotationStreamU public

  --DenotationStream : ∀ {τ} → Val τ → Val (#Stream τ)
  --DenotationStream %Denotation-τ (construct (intrStream (ρ ,, value , closure))) = DenotationStreamU %Denotation-τ closure value
  DenotationStream : ∀ {τ} → Val τ → IntrR (#Stream τ) → Set
  DenotationStream %Denotation-τ (intrStream (ρ ,, value , closure)) = DenotationStreamU %Denotation-τ closure value

  mutual
    !Value : (τ : Type) → Val τ
    !Value (ρ ⇒ τ)       = DenotationArrow (!Value ρ) (!Value τ)
    !Value (#Sum τs)     = DenotationSum (!AllValue τs)
    !Value (#Product τs) = DenotationProduct (!AllValue τs)
    !Value (#Nat)        = DenotationNat
    !Value (#Conat)      = DenotationConat
    --Denotation (#Stream τ)   = DenotationStream (!Value τ)
    !Value (#Stream τ)   (construct rule) = DenotationStream (!Value τ) rule

    !AllValue : (τs : List Type) → AllVal τs
    !AllValue ε = ε
    !AllValue (τ ∷ τs) = !Value τ ∷ !AllValue τs

  lem-AllDenotation : ∀ {τs} {values : All Value τs} → AllPred (!AllValue τs) values → AllAll !Value values
  lem-AllDenotation ε = ε
  lem-AllDenotation (good-value ∷ good-values) = good-value ∷ lem-AllDenotation good-values

  lem-AllDenotation-r : ∀ {τs} {values : All Value τs} → AllAll !Value values → AllPred (!AllValue τs) values
  lem-AllDenotation-r ε = ε
  lem-AllDenotation-r (good-value ∷ good-values) = good-value ∷ lem-AllDenotation-r good-values

  lem-Any-Pred : ∀ {τs} {any-value : Any Value τs} → AllAny !Value any-value → AnyPred (!AllValue τs) any-value
  lem-Any-Pred (here x) = x
  lem-Any-Pred (there allAny) = lem-Any-Pred allAny

  lem-Any-Pred-r : ∀ {τs} {any-value : Any Value τs} → AnyPred (!AllValue τs) any-value → AllAny !Value any-value
  lem-Any-Pred-r {any-value = here x} p = here p
  lem-Any-Pred-r {any-value = there allAny} p = there (lem-Any-Pred-r {any-value = allAny} p)

module _ where
  getAllAnyP :
    {A R : Set} {P Q : A → Set} {P2 : (a : A) → P a → Set} {Q2 : (a : A) → Q a → Set}
    → {as : List A}
    → (W : R → Set)
    → {f : ∀ {a} → P a → Q a → R}
    → {all-p : All P as} → {any-q : Any Q as}
    → AllAll P2 all-p → AllAny Q2 any-q
    → ({a : A} → (Pa : P a) → (Qa : Q a) → P2 a Pa → Q2 a Qa → W (f Pa Qa))
    → W (zipAllAny all-p any-q f)
  getAllAnyP W (x ∷ all-p) (here x₁) ff = ff _ _ x x₁
  getAllAnyP W (x ∷ all-p) (there any-q) ff = getAllAnyP W all-p any-q ff


  !Env : ∀ Γ → Env Γ → Set
  !Env Γ env = AllAll !Value env

  !Step : ∀ τ → Step τ → Set
  !Step τ step = TraceStepF (!Value τ) step

  TraceMachine : ∀ {τ} → Machine τ → Set
  TraceMachine machine = TraceMachineF (!Value _) machine

  TraceThunk : ∀ {τ} → Thunk τ → Set
  TraceThunk thunk = TraceThunkF (!Value _) thunk

  record TraceTermM {Γ τ} (term : TermM Γ τ) : Set where
    constructor mkTraceTermM
    field getTraceTermM : ∀ {env} → !Env Γ env → TraceMachine ((env & term) ∷ ε)
  open TraceTermM public

  !Thunk : ∀ τ → Thunk τ → Set
  !Thunk τ = TraceThunk {τ}

  !Closure : ∀ ρ τ → (closure : Closure ρ τ) → Set
  !Closure ρ τ closure = ∀ {value} → (!value : !Value ρ value) → !Thunk τ (composeValueClosure value closure)

  !CallStack : ∀ σ τ → CallStack σ τ → Set
  !CallStack σ τ stack = ∀ {value} → !Value σ value → !Step τ (composeValueStack value stack)

  ◽_ : ∀ {τ value} → !Value τ value → !Step τ (finish value)
  ◽_ = !finish

  ∗_ : ∀ {τ machine} → !Step τ (reduce machine) → !Step τ (continue machine)
  ∗_ = !continue

  !composeValueClosure : ∀ {σ τ value closure} → !Value σ value → !Closure σ τ closure → !Thunk τ (composeValueClosure value closure)
  !composeValueClosure !value !closure = !closure !value

  !composeValueStack : ∀ {σ τ value stack} → !Value σ value → !CallStack σ τ stack → !Step τ (composeValueStack value stack)
  !composeValueStack !value !stack = !stack !value

  !composeStepStack : ∀ {σ τ step stack} → !Step σ step → !CallStack σ τ stack → !Step τ (composeStepStack step stack)
  !composeStepStack (!finish !value) !stack = !stack !value
  !composeStepStack {σ} {τ} {continue machine} {stack} (!continue !machine) !stack = ∗ (transport (!Step _) (lem-step machine stack) (!composeStepStack !machine !stack))

  ▹ : ∀ {σ τ} {thunk : Thunk σ} {stack} → TraceThunk thunk → !CallStack σ τ stack → !Step τ (reduce (thunk ∷ stack))
  ▹ {thunk = thunk} {stack} (mkTraceMachineF trace-step) trace-stack = transport (!Step _) (lem-step (thunk ∷ ε) stack) (!composeStepStack trace-step trace-stack)

  applyDenotation : ∀ {σ τ function value} → !Value (σ ⇒ τ) function → !Value σ value → !Thunk τ (applyValue function value)
  applyDenotation {function = construct (intrArrow x)} ~f ~v = mkTraceMachineF (∗ ▹ (~f ~v) \ ~v' → ∗ ◽ ~v')

module _ where
  !constructArrow : ∀ {ρ τ rule} → AllIntr !Closure !Value (ρ ⇒ τ) rule → !Value (ρ ⇒ τ) (construct rule)
  --!constructArrow (mkAllIntrArrow (!mkClosure !closure)) = \ !value → !closure !value
  !constructArrow (mkAllIntrArrow !closure) = \ !value → !closure !value

  !constructSum : ∀ {τs rule} → AllIntr !Closure !Value (#Sum τs) rule → !Value (#Sum τs) (construct rule)
  !constructSum (mkAllIntrSum !v) = lem-Any-Pred !v

  !constructProduct : ∀ {τs rule} → AllIntr !Closure !Value (#Product τs) rule → !Value (#Product τs) (construct rule)
  !constructProduct (mkAllIntrProduct !vs) = lem-AllDenotation-r !vs

  !constructNat : ∀ {rule} → AllIntr !Closure !Value #Nat rule → !Value #Nat (construct rule)
  !constructNat {intrNat v} (mkAllIntrNat !v) = !mkNat (to-Good-Maybe DenotationNat v !v)

  !constructConat : ∀ {rule} → AllIntr !Closure !Value #Conat rule → !Value #Conat (construct rule)
  forceConat (!constructConat {intrConat (ρ ,, v , s)} (mkAllIntrConat (.ρ ,, ~v , ~s))) =
      --mapFoo (applyDenotation ~s ~v)
      mkTraceMachineF (mapFoo (getTraceMachineF (applyDenotation ~s ~v)))
    where 
      foo : ∀ value → !Value (#Maybe ρ) value → DenotationMaybe (DenotationConatU s) value
      foo v'@(construct (intrSum (here x))) ~v' = tt
      foo v'@(construct (intrSum (there (here x)))) ~v' = !constructConat {intrConat (ρ ,, x , s)} (mkAllIntrConat (ρ ,, ~v' , ~s))

      mapFoo : {step : Step (#Maybe ρ)} → TraceStepF (!Value (#Maybe ρ)) step → TraceStepF (DenotationMaybe (DenotationConatU s)) step
      mapFoo {step = finish v}   (!finish x) = !finish (foo v x)
      mapFoo {step = continue m} (!continue trace) = !continue (mapFoo trace)

  !constructStream : ∀ {τ rule} → AllIntr !Closure !Value (#Stream τ) rule → !Value (#Stream τ) (construct rule)
  forceStream (!constructStream {τ} {intrStream (ρ ,, v , s)} (mkAllIntrStream (.ρ ,, ~v , ~s))) =
      --mapFoo (applyDenotation ~s ~v)
      mkTraceMachineF (mapFoo (getTraceMachineF (applyDenotation ~s ~v)))
    where 
      foo :
        (value : Value (#Pair τ ρ)) → DenotationProduct (!Value τ ∷ !Value ρ ∷ ε) value
        → DenotationPair (!Value τ) (DenotationStreamU (!Value τ) s) value
      foo (construct (intrProduct (a ∷ b ∷ ε))) (~a ∷ ~b ∷ ε) = ~a , !constructStream (mkAllIntrStream (ρ ,, ~b , ~s)) , tt

      mapFoo : {step : Step (#Pair τ ρ)} → TraceStepF (DenotationProduct (!Value τ ∷ !Value ρ ∷ ε)) step → TraceStepF (DenotationPair (!Value τ) (DenotationStreamU (!Value τ) s)) step
      mapFoo (!finish x) = !finish (foo _ x)
      mapFoo (!continue trace) = !continue (mapFoo trace)

  !construct : ∀ {τ rule} → AllIntr !Closure !Value τ rule → !Value τ (construct rule)
  !construct {ρ ⇒ τ}       = !constructArrow
  !construct {#Sum τs}     = !constructSum
  !construct {#Product τs} = !constructProduct
  !construct {#Nat}        = !constructNat
  !construct {#Conat}      = !constructConat
  !construct {#Stream τ}   = !constructStream

module _ where
  !eliminateArrow : ∀ {ρ τ ϕ} rule value → AllElim !Value (ρ ⇒ τ) ϕ rule → !Value (ρ ⇒ τ) value → !Thunk ϕ (eliminate rule value)
  !eliminateArrow _ (construct (intrArrow _)) (mkAllElimArrow !v) !f = !f !v

  !eliminateSum : ∀ {τs ϕ} rule value → AllElim !Value (#Sum τs) ϕ rule → !Value (#Sum τs) value → !Thunk ϕ (eliminate rule value)
  !eliminateSum _ (construct (intrSum _)) (mkAllElimSum !fs) !v =
    getAllAnyP TraceThunk
      !fs (lem-Any-Pred-r !v)
      \{ (construct (intrArrow _)) _ !f !v → mkTraceMachineF (∗ ▹ (!f !v) \ !v' → ∗ ◽ !v') }

  !eliminateProduct :
      ∀ {τs ϕ} rule value → AllElim !Value (#Product τs) ϕ rule → !Value (#Product τs) value
      → !Thunk ϕ (eliminate rule value)
  !eliminateProduct (elimProduct i) (construct (intrProduct _)) mkAllElimProduct ~vs = mkTraceMachineF (◽ get2 (lem-AllDenotation ~vs) i)

  !eliminateNat : ∀ {ϕ} rule value → AllElim !Value #Nat ϕ rule → !Value #Nat value → !Thunk ϕ (eliminate rule value)
  getTraceMachineF (!eliminateNat (elimNat s@(construct (intrArrow _))) (construct (intrNat (construct (intrSum (here v))))) (mkAllElimNat ~s) ~v) =
      ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ▹ (~s ε) \ ~v' →
      ∗ ◽ ~v'
  getTraceMachineF (!eliminateNat (elimNat s@(construct (intrArrow _))) (construct (intrNat (construct (intrSum (there (here n)))))) (mkAllElimNat ~s) (!mkNat ~n)) =
      ∗ ∗ ∗ ∗ ∗ ▹ (!eliminateNat (elimNat s) n (mkAllElimNat ~s) ~n) \ ~v' →
      ∗ ∗ ∗ ∗ ∗ ▹ (~s ~v') \ ~v'' →
      ∗ ◽ ~v''

  !eliminateConat : ∀ {ϕ} rule value → AllElim !Value #Conat ϕ rule → !Value #Conat value → !Thunk ϕ (eliminate rule value)
  !eliminateConat rule value x x₁ = {!!}

  !eliminateStream :
      ∀ {τ ϕ} rule value → AllElim !Value (#Stream τ) ϕ rule → !Value (#Stream τ) value
      → !Thunk ϕ (eliminate rule value)
  !eliminateStream = {!!}

  !eliminate : ∀ {τ ϕ rule value} → AllElim !Value τ ϕ rule → !Value τ value → !Thunk ϕ (eliminate rule value)
  !eliminate {ρ ⇒ τ}       = !eliminateArrow _ _
  !eliminate {#Sum τs}     = !eliminateSum _ _
  !eliminate {#Product τs} = !eliminateProduct _ _
  !eliminate {#Nat}        = !eliminateNat _ _
  !eliminate {#Conat}      = !eliminateConat _ _
  !eliminate {#Stream τ}   = !eliminateStream _ _

module _ where
  !plugEnvIntr :
    ∀ {Γ τ} {env} {rule : IntrM Γ τ}
    → !Env Γ env → AllIntr (\ρ τ → TraceTermM {ρ ∷ Γ} {τ}) (\_ _ → ⊤) τ rule → AllIntr !Closure !Value τ (plugEnvIntr env rule)
  !plugEnvIntr {env = env} {rule = rule} !env all-trace =
      allMapIntr
        --(\term → env & term) TraceTermM !Closure (\trace-term → !mkClosure (\ !v → getTraceTermM trace-term (!v ∷ !env)))
        (\term → env & term) (\ρ τ → TraceTermM {ρ ∷ _} {τ}) !Closure (\trace-term → \ !v → getTraceTermM trace-term (!v ∷ !env))
        (\x → get env x) (\_ _ → ⊤) !Value (\{τ} {x} _ → get2 !env x) rule
        all-trace

  !plugEnvElim :
      ∀ {Γ τ ϕ} {env} {rule : ElimM Γ τ ϕ}
      → !Env Γ env → AllElim !Value τ ϕ (plugEnvElim env rule)
  !plugEnvElim {env = env} {rule = rule} !env =
      (allMapElim
        (\x → get env x) (\_ _ → ⊤) !Value (\{τ'} {x'} _ → get2 !env x') rule
        (buildAllElim (\_ → tt) rule)
      )

  mutual
    allGoodIntr : ∀ {Γ τ} → (rule : IntrM Γ τ) → AllIntr (\ρ τ → TraceTermM {ρ ∷ Γ} {τ}) (\_ _ → ⊤) τ rule
    allGoodIntr (intrArrow term)   = mkAllIntrArrow (mkTraceTermM (\{env} good-env → mkTraceMachineF (traceMachine term env ε good-env \good-value → ◽ good-value)))
    allGoodIntr (intrSum rule)     = mkAllIntrSum (buildAllAny (\_ → tt) rule)
    allGoodIntr (intrProduct rule) = mkAllIntrProduct (buildAllAll (\_ → tt) rule)
    allGoodIntr (intrNat rule)     = mkAllIntrNat tt
    allGoodIntr (intrConat rule)   = mkAllIntrConat (_ ,, (tt , tt))
    allGoodIntr (intrStream rule)  = mkAllIntrStream (_ ,, (tt , tt))

    traceMachine :
      ∀ {Γ τ ϕ} → (term : TermM Γ τ) → ∀ env stack
      → !Env Γ env → !CallStack τ ϕ stack
      → !Step ϕ (reduce ((env & term) ∷ stack))
    traceMachine (return x) env ε !env !stack = ◽ (get2 !env x)
    traceMachine (return x) env ((env' & term) ∷ stack) !env !stack = !stack (get2 !env x)
    traceMachine (intr rule ▸ cont) env stack !env !stack = ∗ traceMachine cont _ _ (!value ∷ !env) !stack
      where
        !value : !Value _ (construct (plugEnvIntr env rule))
        !value = !construct (!plugEnvIntr !env (allGoodIntr rule))
    traceMachine (elim x rule ▸ term) env stack !env !stack = ∗ ▹ !thunk \ !v → ∗ traceMachine term _ _ (!v ∷ !env) !stack
      where
        !thunk : !Thunk _ (eliminate (plugEnvElim env rule) (get env x))
        !thunk = !eliminate (!plugEnvElim {rule = rule} !env) (get2 !env x)

  denoteValue : ∀ {τ} → (value : Value τ) → !Value τ value
  denoteValue = {!!}

  denoteEnv : ∀ {Γ} → (env : Env Γ) → !Env Γ env
  denoteEnv ε = ε
  denoteEnv (value ∷ env) = denoteValue value ∷ denoteEnv env

  denoteStack : ∀ {ρ τ} → (stack : CallStack ρ τ) → !CallStack ρ τ stack
  denoteStack ε = \ !v → !finish !v
  denoteStack ((env & term) ∷ stack) = \ !v → !continue (traceMachine term _ _ (!v ∷ denoteEnv env) (denoteStack stack))

  run : ∀ {τ} → (machine : Machine τ) → TraceMachine machine
  run ((env & term) ∷ stack) = {!!}

  run' : ∀ {τ} → (term : TermM ε τ) → TraceMachine ((ε & term) ∷ ε)
  --run' term = traceMachine term ε ε ε ◽_
  run' term = mkTraceMachineF (traceMachine term ε ε ε ◽_)

  resultStep : ∀ {τ} {step : Step τ} → !Step τ step → Value τ
  resultStep {step = finish value}     (!finish !value)  = value
  resultStep {step = continue machine} (!continue trace) = resultStep trace

  result : ∀ {τ} {machine : Machine τ} → TraceMachine machine → Value τ
  result (mkTraceMachineF trace) = resultStep trace

evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))

module Test where
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
