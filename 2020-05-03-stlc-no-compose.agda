module _ where -- ma look no imports

{-
  mutual
    mapCompileAll : ∀ {Γ τs} → (κ : Type → Type) → All (\τ → Term Γ (κ τ)) τs → All (\τ → TermM Γ (κ τ)) τs
    mapCompileAll κ  ε       = ε
    mapCompileAll κ (v ∷ vs) = compile v ∷ mapCompileAll κ vs

    mapCompileAny : ∀ {Γ τs} → (κ : Type → Type) → Any (\τ → Term Γ (κ τ)) τs → Any (\τ → TermM Γ (κ τ)) τs
    mapCompileAny κ (here v)   = here (compile v)
    mapCompileAny κ (there vᵢ) = there (mapCompileAny κ vᵢ)

    mapCompileIntr : ∀ {Γ τ} → Intr (AbsTerm Γ) (Term Γ) τ → Intr (AbsTermM Γ) (TermM Γ) τ
    mapCompileIntr (intrArrow e)              = intrArrow (compile e)
    mapCompileIntr (intrSum vᵢ)               = intrSum (mapCompileAny identity vᵢ)
    mapCompileIntr (intrProduct vs)           = intrProduct (mapCompileAll identity vs)
    mapCompileIntr (intrNat v)                = intrNat (compile v)
    mapCompileIntr (intrConat (ρ ,, v , f))   = intrConat (ρ ,, compile v , compile f)
    mapCompileIntr (intrStream (ρ ,, v , f))  = intrStream (ρ ,, compile v , compile f)

    mapCompileElim : ∀ {Γ τ ϕ} → Elim (Term Γ) τ ϕ → Elim (TermM Γ) τ ϕ
    mapCompileElim (elimArrow v)   = elimArrow (compile v)
    mapCompileElim (elimSum fs)    = elimSum (mapCompileAll (\τ → τ ⇒ _) fs)
    mapCompileElim (elimProduct i) = elimProduct i
    mapCompileElim (elimNat f)     = elimNat (compile f)
    mapCompileElim  elimConat      = elimConat
    mapCompileElim  elimStream     = elimStream

  mapCompileExpr : ∀ {Γ τ} → Expr (AbsTerm Γ) (Term Γ) τ → Expr (AbsTermM Γ) (TermM Γ) τ
    mapCompileExpr (intr rule) = intr (mapCompileIntr rule)
    mapCompileExpr (elim v rule) = elim (compile v) (mapCompileElim rule)
-}

-- 1. Generic library definitions
module _ where
  data ⊥ : Set where
  
  record ⊤ : Set where
    constructor tt

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

  infixr 5 _++_
  _++_ : {A : Set} → List A → List A → List A
  ε ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  has-skip : ∀ {Ω : Set} {τs τ} → (ρs : List Ω) → Has τs τ → Has (ρs ++ τs) τ
  has-skip  ε       i = i
  has-skip (ρ ∷ ρs) i = there (has-skip ρs i)

  has-append : ∀ {Ω : Set} {τs τ} → (ρs : List Ω) → Has τs τ → Has (τs ++ ρs) τ
  has-append ρs (here e)  = here e
  has-append ρs (there i) = there (has-append ρs i)

  has-splice : ∀ {Ω : Set} {τ} → (τs τs' ρs : List Ω) → Has (τs ++ τs') τ → Has (τs ++ ρs ++ τs') τ
  has-splice  ε       τs' ρs  i        = has-skip ρs i
  has-splice (τ ∷ τs) τs' ρs (here e)  = here e
  has-splice (τ ∷ τs) τs' ρs (there i) = there (has-splice τs τs' ρs i)

  has-abs : ∀ {Ω : Set} {τ} → (ϕ : Ω) → (τs ρs : List Ω) → Has (ϕ ∷ τs) τ → Has (ϕ ∷ ρs ++ τs) τ
  has-abs ϕ τs ρs i = has-splice (ϕ ∷ ε) τs ρs i

  has-cons : {Ω : Set} {τs : List Ω} {τ ϕ : Ω} → Has τs τ → Has (τ ∷ τs) ϕ → Has τs ϕ
  has-cons i (here refl) = i
  has-cons i (there j) = j

  has-prepend : {A : Set} {as as' : List A} → (∀ {r} → Has as r → Has as' r) → (cs : List A) → (∀ {r} → Has (cs ++ as) r → Has (cs ++ as') r)
  has-prepend f ε x = f x
  has-prepend f (c ∷ cs) (here x) = here x
  has-prepend f (c ∷ cs) (there x) = there (has-prepend f cs x)

  $0 : ∀ {A a0 as}             → Has {A} (a0 ∷ as) a0
  $1 : ∀ {A a0 a1 as}          → Has {A} (a0 ∷ a1 ∷ as) a1
  $2 : ∀ {A a0 a1 a2 as}       → Has {A} (a0 ∷ a1 ∷ a2 ∷ as) a2
  $3 : ∀ {A a0 a1 a2 a3 as}    → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ as) a3
  $4 : ∀ {A a0 a1 a2 a3 a4 as} → Has {A} (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ as) a4
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

  zipAllAnyP :
    {A R : Set} {P Q : A → Set} {P2 : (a : A) → P a → Set} {Q2 : (a : A) → Q a → Set}
    → {as : List A}
    → (W : R → Set)
    → {f : ∀ {a} → P a → Q a → R}
    → {all-p : All P as} → {any-q : Any Q as}
    → AllAll P2 all-p → AllAny Q2 any-q
    → ({a : A} → (Pa : P a) → (Qa : Q a) → P2 a Pa → Q2 a Qa → W (f Pa Qa))
    → W (zipAllAny all-p any-q f)
  zipAllAnyP W (x ∷ all-p) (here x₁) ff = ff _ _ x x₁
  zipAllAnyP W (x ∷ all-p) (there any-q) ff = zipAllAnyP W all-p any-q ff

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
  
  data Expr (%F : Type → Type → Set) (%V : Type → Set) (τ : Type) : Set where
    intr : Intr %F %V τ               → Expr %F %V τ
    elim : ∀ {ϕ} → %V ϕ → Elim %V ϕ τ → Expr %F %V τ

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

  mapExpr :
    ∀ {%F1 %F2 %V1 %V2} → (%mapF : ∀ {ρ τ} → %F1 ρ τ → %F2 ρ τ) → (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
    → (∀ {τ} → Expr %F1 %V1 τ → Expr %F2 %V2 τ)
  mapExpr %mapF %mapV (intr rule)       = intr (mapIntr %mapF %mapV rule)
  mapExpr %mapF %mapV (elim value rule) = elim (%mapV value) (mapElim %mapV rule)

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
      mkAllElimProduct : ∀ {τs τ} i                               → AllElim _ _ (elimProduct {%V} {τs} {τ} i)
      mkAllElimNat     : ∀ {ϕ rule} → %AllV _ rule                     → AllElim _ _ (elimNat {%V} {ϕ} rule)
      mkAllElimConat   :                                               AllElim _ _ (elimConat)
      mkAllElimStream  : ∀ {τ}                                       → AllElim _ _ (elimStream {%V} {τ})

  {-
  module _
      {%F : Type → Type → Set} {%V : Type → Set}
      (%AllF : ∀ {ρ τ} → %F ρ τ → Set) (%AllV : ∀ {τ} → %V τ → Set)
    where
    data AllExpr : ∀ {τ} → Expr %F %V τ → Set where
      mkAllIntr : ∀ {τ} {rule : Intr %F %V τ} → AllIntr %AllF %AllV _ rule → AllExpr (intr rule)
      mkAllElim : ∀ {ρ τ} {value : %V ρ} {rule : Elim %V ρ τ} → %AllV value → AllElim %AllV _ _ rule → AllExpr (elim value rule)
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
    mapAllIntr : ∀ {τ} → (intr1 : Intr %F1 %V1 τ) → AllIntr %AllF1 %AllV1 τ intr1 → AllIntr %AllF2 %AllV2 τ (mapIntr %mapF %mapV intr1)
    mapAllIntr _   (mkAllIntrArrow all) = mkAllIntrArrow (%allMapF all)
    mapAllIntr _     (mkAllIntrSum all) = mkAllIntrSum (allMapAny %mapV _ _ %allMapV all)
    mapAllIntr _ (mkAllIntrProduct all) = mkAllIntrProduct (allMapAll %mapV _ _ %allMapV all)
    mapAllIntr _     (mkAllIntrNat all) = mkAllIntrNat (%allMapV all)
    mapAllIntr _   (mkAllIntrConat all) = mkAllIntrConat (allMapΣ (map× %mapV %mapV) _ _ (allMap× %mapV %mapV (%AllV1 _) (%AllV2 _) (%AllV1 _) (%AllV2 _) %allMapV %allMapV) all)
    mapAllIntr _  (mkAllIntrStream all) = mkAllIntrStream (allMapΣ (map× %mapV %mapV) _ _ (allMap× %mapV %mapV (%AllV1 _) (%AllV2 _) (%AllV1 _) (%AllV2 _) %allMapV %allMapV) all)

  module _
      {%V1 %V2 : Type → Set}
      (%mapV : ∀ {τ} → %V1 τ → %V2 τ)
      (%AllV1 : ∀ τ → %V1 τ → Set)
      (%AllV2 : ∀ τ → %V2 τ → Set)
      (%allMapV : ∀ {τ} {v1 : %V1 τ} → %AllV1 τ v1 → %AllV2 τ (%mapV v1))
    where
    mapAllElim : ∀ {τ ϕ} → (elim1 : Elim %V1 τ ϕ) → AllElim %AllV1 τ ϕ elim1 → AllElim %AllV2 τ ϕ (mapElim %mapV elim1)
    mapAllElim _ (mkAllElimArrow all) = mkAllElimArrow (%allMapV all)
    mapAllElim _ (mkAllElimSum all)   = mkAllElimSum (allMapAll %mapV _ _ %allMapV all)
    mapAllElim _  (mkAllElimProduct i)    = mkAllElimProduct i
    mapAllElim _ (mkAllElimNat all)   = mkAllElimNat (%allMapV all)
    mapAllElim _  mkAllElimConat      = mkAllElimConat
    mapAllElim _  mkAllElimStream     = mkAllElimStream

  module _ {%V : Type → Set} {%PredV : ∀ τ → %V τ → Set} (%allV : ∀ {τ} → (v : %V τ) → %PredV τ v) where
    buildAllElim : ∀ {τ ϕ} → (rule : Elim %V τ ϕ) → AllElim %PredV τ ϕ rule
    buildAllElim (elimArrow rule)   = mkAllElimArrow (%allV rule)
    buildAllElim (elimSum rule)     = mkAllElimSum (buildAllAll %allV rule)
    buildAllElim (elimProduct rule) = mkAllElimProduct rule
    buildAllElim (elimNat rule)     = mkAllElimNat (%allV rule)
    buildAllElim  elimConat         = mkAllElimConat
    buildAllElim  elimStream        = mkAllElimStream

-- regular term representation
module _ where
  mutual
    -- regular de-bruijn term
    data Term (Γ : List Type) (τ : Type) : Set where
      var  : Has Γ τ → Term Γ τ
      wrap : Expr (AbsTerm Γ) (Term Γ) τ → Term Γ τ
  
    AbsTerm : List Type → (Type → Type → Set)
    AbsTerm Γ ρ τ = Term (ρ ∷ Γ) τ

  {-# TERMINATING #-} -- terminating because it preserves structure
  mapTerm : ∀ {Γ Δ} → (∀ {τ} → Has Γ τ → Has Δ τ) → (∀ {τ} → Term Γ τ → Term Δ τ)
  mapTerm f (var x) = var (f x)
  mapTerm f (wrap expr) = wrap (mapExpr (mapTerm (has-prepend f _)) (mapTerm f) expr)

  ↑_ : ∀ {Γ ρ τ} → Term Γ τ → Term (ρ ∷ Γ) τ
  ↑ term = mapTerm there term

  #lambda : ∀ {Γ σ τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  #lambda f = wrap (intr (intrArrow f))

  #apply : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  #apply f v = wrap (elim f (elimArrow v))
                        
  #compose : ∀ {Γ ρ σ τ} → Term Γ (ρ ⇒ σ) → Term Γ (σ ⇒ τ) → Term Γ (ρ ⇒ τ)
  #compose f g = #lambda (#apply (↑ g) (#apply (↑ f) (var $0)))
  
  #inl : ∀ {Γ σ τ} → Term Γ σ → Term Γ (#Either σ τ)
  #inl v = wrap (intr (intrSum (here v)))
  
  #inr : ∀ {Γ σ τ} → Term Γ τ → Term Γ (#Either σ τ)
  #inr v = wrap (intr (intrSum (there (here v))))
  
  #either : ∀ {Γ σ τ ϕ} → Term Γ (σ ⇒ ϕ) → Term Γ (τ ⇒ ϕ) → Term Γ (#Either σ τ) → Term Γ ϕ
  #either f1 f2 v = wrap (elim v (elimSum (f1 ∷ f2 ∷ ε)))
  
  #unit : ∀ {Γ} → Term Γ #Unit
  #unit = wrap (intr (intrProduct ε))
  
  #pair : ∀ {Γ σ τ} → Term Γ σ → Term Γ τ → Term Γ (#Pair σ τ)
  #pair v1 v2 = wrap (intr (intrProduct (v1 ∷ v2 ∷ ε)))

  #fst : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ σ
  #fst v = wrap (elim v (elimProduct $0))

  #snd : ∀ {Γ σ τ} → Term Γ (#Pair σ τ) → Term Γ τ
  #snd v = wrap (elim v (elimProduct $1))

  #mapPair : ∀ {Γ ρ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Pair ρ σ ⇒ #Pair ρ τ)
  #mapPair f = #lambda (#pair (#fst (var $0)) (#apply (↑ f) (#snd (var $0))))

  #nothing : ∀ {Γ τ} → Term Γ (#Maybe τ)
  #nothing = #inl #unit

  #just : ∀ {Γ τ} → Term Γ τ → Term Γ (#Maybe τ)
  #just a = #inr a

  #maybe : ∀ {Γ τ ϕ} → Term Γ ϕ → Term Γ (τ ⇒ ϕ) → Term Γ (#Maybe τ) → Term Γ ϕ
  #maybe f1 f2 v = #either (#lambda (↑ f1)) f2 v

  #mapMaybe : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (#Maybe σ ⇒ #Maybe τ)
  #mapMaybe f = #lambda (#maybe #nothing (#lambda (#just (#apply (↑ ↑ f) (var $0)))) (var $0))

  #elimNat : ∀ {Γ ϕ} → Term Γ (#Maybe ϕ ⇒ ϕ) → Term Γ (#Nat ⇒ ϕ)
  #elimNat f = #lambda (wrap (elim (var $0) (elimNat (↑ f))))

  #buildConat : ∀ {Γ ρ} → Term Γ (ρ ⇒ #Maybe ρ) → Term Γ (ρ ⇒ #Conat)
  #buildConat f = #lambda (wrap (intr (intrConat (_ ,, var $0 , ↑ f))))

  #buildStream : ∀ {Γ τ ρ} → Term Γ (ρ ⇒ #Pair τ ρ) → Term Γ (ρ ⇒ #Stream τ)
  #buildStream f = #lambda (wrap (intr (intrStream (_ ,, var $0 , ↑ f))))

-- compiled term representation
module _ where
  infixr 5 _▸_
  mutual
    data TermM (Γ : List Type) (τ : Type) : Set where
      return : Has Γ τ → TermM Γ τ
      _▸_    : ∀ {ρ} → Expr (AbsTermM Γ) (Has Γ) ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ

    AbsTermM : List Type → (Type → Type → Set)
    AbsTermM Γ σ τ = TermM (σ ∷ Γ) τ

  -- compile-time introduction rule
  IntrM : List Type → Type → Set
  IntrM Γ τ = Intr (AbsTermM Γ) (Has Γ) τ

  -- compile-time elimination rule
  ElimM : List Type → Type → Type → Set
  ElimM Γ τ ϕ = Elim (Has Γ) τ ϕ

  -- maps a function to each variable in a term
  {-# TERMINATING #-} -- terminating because it preserves structure
  mapTermM : ∀ {Γ Δ τ} → (∀ {ϕ} → Has Γ ϕ → Has Δ ϕ) → (TermM Γ τ → TermM Δ τ)
  mapTermM f (return x) = return (f x)
  mapTermM f (expr ▸ term) = mapExpr (mapTermM (has-prepend f _)) f expr ▸ mapTermM (has-prepend f _) term

  -- term consisting of a single expression
  pure : ∀ {Γ τ} → Expr (AbsTermM Γ) (Has Γ) τ → TermM Γ τ
  pure expr = expr ▸ return $0

-- compilation
module _ where
  {-
     The actual implementation is not interesting and is provided without comments, feel free to skip to the end of the section.
  -}
  infixr 5 _∷ₗ_
  data Linear {Ω : Set} (%V : Ω → Set) (%E : List Ω → Set) : List Ω → Set where
    εₗ   : ∀ {ρs} → %E ρs → Linear %V %E ρs
    _∷ₗ_ : ∀ {ρ ρs} → %V ρ → Linear %V %E (ρ ∷ ρs) → Linear %V %E ρs

  mapLinear :
      {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set}
      → (∀ {τs} → %E1 τs → %E2 τs) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 τs)
  mapLinear f (εₗ x)   = εₗ (f x)
  mapLinear f (v ∷ₗ l) = v ∷ₗ mapLinear f l

  mapLinear' :
      {Ω : Set} {%V : Ω → Set} {%E1 %E2 : List Ω → Set} {Γ : List Ω}
      → (∀ {τs} → %E1 τs → %E2 (τs ++ Γ)) → (∀ {τs} → Linear %V %E1 τs → Linear %V %E2 (τs ++ Γ))
  mapLinear' f (εₗ x)   = εₗ (f x)
  mapLinear' f (v ∷ₗ l) = v ∷ₗ mapLinear' f l

  linizeAny :
      {Ω : Set} {%V : Ω → Set} {τs : List Ω}
      → (κ : Ω → Ω) → Any (\τ → %V (κ τ)) τs → Linear %V (\ρs → Any (\τ → Has ρs (κ τ)) τs) ε
  linizeAny κ (here v)   = v ∷ₗ εₗ (here $0)
  linizeAny κ (there vᵢ) = mapLinear there (linizeAny κ vᵢ)

  linizeAll :
      {Ω : Set} {%V : Ω → Set} {τs : List Ω}
      → (κ : Ω → Ω) → All (\τ → %V (κ τ)) τs → Linear %V (\ρs → All (\τ → Has ρs (κ τ)) τs) ε
  linizeAll κ  ε       = εₗ ε
  linizeAll κ (v ∷ vs) = v ∷ₗ mapLinear' (\vs' → has-skip _ $0 ∷ mapAll (has-append _) vs') (linizeAll κ vs)

  linizeIntr : ∀ {%F %V τ} → Intr %F %V τ → Linear %V (\ρs → Intr %F (Has ρs) τ) ε
  linizeIntr (intrArrow e)             = εₗ (intrArrow e)
  linizeIntr (intrSum vᵢ)              = mapLinear intrSum (linizeAny identity vᵢ)
  linizeIntr (intrProduct vs)          = mapLinear intrProduct (linizeAll identity vs)
  linizeIntr (intrNat v)               = v ∷ₗ εₗ (intrNat $0)
  linizeIntr (intrConat (ρ ,, v , f))  = v ∷ₗ f ∷ₗ εₗ (intrConat (ρ ,, $1 , $0))
  linizeIntr (intrStream (ρ ,, v , f)) = v ∷ₗ f ∷ₗ εₗ (intrStream (ρ ,, $1 , $0))

  linizeElim : ∀ {%V τ ϕ} → Elim %V τ ϕ → Linear %V (\ρs → Elim (Has ρs) τ ϕ) ε
  linizeElim (elimArrow v)    = v ∷ₗ εₗ (elimArrow $0)
  linizeElim (elimSum f)      = mapLinear elimSum (linizeAll (\τ → τ ⇒ _) f)
  linizeElim (elimProduct i)  = εₗ (elimProduct i)
  linizeElim (elimNat v)      = v ∷ₗ εₗ (elimNat $0)
  linizeElim  elimConat       = εₗ elimConat
  linizeElim  elimStream      = εₗ elimStream

  linizeExpr : ∀ {%F %V τ} → Expr %F %V τ → Linear %V (\ρs → Expr %F (Has ρs) τ) ε
  linizeExpr (intr rule)       = mapLinear intr (linizeIntr rule)
  linizeExpr (elim value rule) = value ∷ₗ mapLinear' (\rule' → elim (has-skip _ $0) (mapElim (has-append _) rule')) (linizeElim rule)

  combine2 : ∀ {Γ ρ τ} → TermM Γ ρ → TermM (ρ ∷ Γ) τ → TermM Γ τ
  combine2 (return x)     term2 = mapTermM (has-cons x) term2
  combine2 (expr ▸ term1) term2 = expr ▸ combine2 term1 (mapTermM (has-abs _ _ _) term2)

  combineL : ∀ {Γ Δ τ} → Linear (TermM Γ) (\ρs → Expr (AbsTermM Γ) (Has ρs) τ) Δ → TermM (Δ ++ Γ) τ
  combineL (εₗ expr)   = pure (mapExpr (mapTermM (has-abs _ _ _)) (has-append _) expr)
  combineL (term ∷ₗ l) = combine2 (mapTermM (has-skip _) term) (combineL l)

  seqize : ∀ {Γ τ} → Expr (AbsTermM Γ) (TermM Γ) τ → TermM Γ τ
  seqize expr = combineL (linizeExpr expr)

  -- transforms regular representation of a term into compiled representation
  {-# TERMINATING #-} -- terminating because `mapExpr` preserves structure
  compile : ∀ {Γ τ} → Term Γ τ → TermM Γ τ
  compile (var x)     = return x
  compile (wrap expr) = seqize (mapExpr compile compile expr)


-- run-time term representation
module _ where
  mutual
    data Value (τ : Type) : Set where
      construct : Intr Closure Value τ → Value τ

    data Closure (ρ τ : Type) : Set where
      _&_ : ∀ {Γ} → Env Γ → TermM (ρ ∷ Γ) τ → Closure ρ τ

    -- a list of values for each type in Γ
    Env : List Type → Set
    Env Γ = All Value Γ

  -- run-time introduction rule
  IntrR : Type → Set
  IntrR τ = Intr Closure Value τ

  -- run-time elimination rule
  ElimR : Type → Type → Set
  ElimR τ ϕ = Elim Value τ ϕ

  -- a term and an environment of values for each variable it references
  data Thunk (τ : Type) : Set where
    _&_ : ∀ {Γ} → Env Γ → TermM Γ τ → Thunk τ

  -- a composable sequence of closures
  data CallStack : Type → Type → Set where
    ε   : ∀ {τ}     → CallStack τ τ
    _∷_ : ∀ {ρ σ τ} → Closure ρ σ → CallStack σ τ → CallStack ρ τ

  -- computation state
  -- * a thunk that is currently being evaluated
  -- * and a continuation which will be applied when we finish evaluating the thunk
  data Machine : Type → Set where
    _▹_ : ∀ {σ τ} → Thunk σ → CallStack σ τ → Machine τ

  -- result of a single computation step
  -- * final value if the computation finishes
  -- * next computation state if it doesn't
  data Step (τ : Type) : Set where
    finish   : Value τ → Step τ
    continue : Machine τ → Step τ

  -- plugs a value into a closure, producing a thunk
  composeValueClosure : ∀ {σ τ} → Value σ → Closure σ τ → Thunk τ
  composeValueClosure value (env & term) = (value ∷ env) & term

  -- composes two callstacks
  composeStackStack : ∀ {ρ σ τ} → CallStack ρ σ → CallStack σ τ → CallStack ρ τ
  composeStackStack  ε                 stack2 = stack2
  composeStackStack (closure ∷ stack1) stack2 = closure ∷ composeStackStack stack1 stack2

  -- appends a callstack to the current callstack of a machine
  composeMachineStack : ∀ {σ τ} → Machine σ → CallStack σ τ → Machine τ
  composeMachineStack (thunk ▹ stack1) stack2 = thunk ▹ composeStackStack stack1 stack2

  -- applies a value to a callstack
  composeValueStack : ∀ {σ τ} → Value σ → CallStack σ τ → Step τ
  composeValueStack value  ε                = finish value
  composeValueStack value (closure ∷ stack) = continue (composeValueClosure value closure ▹ stack)

  -- composes a computation step and a callstack
  -- * for a finished computation: applies the callstack to the result
  -- * for a non-finished computation: append the callstack the current callstack of the machine
  composeStepStack : ∀ {σ τ} → Step σ → CallStack σ τ → Step τ
  composeStepStack (finish value)     stack = composeValueStack value stack
  composeStepStack (continue machine) stack = continue (composeMachineStack machine stack)

  -- transforms compiled representation of a closed term into run-time representation
  -- * initial environment is empty
  -- * initial continuation is empty as well
  load : ∀ {τ} → TermM ε τ → Machine τ
  load term = (ε & term) ▹ ε

-- operational semantics for elimination rules
module _ where
  eliminateArrow : ∀ {ρ τ ϕ} → Elim Value (ρ ⇒ τ) ϕ → Value (ρ ⇒ τ) → Thunk ϕ
  eliminateArrow (elimArrow value) (construct (intrArrow closure)) = composeValueClosure value closure

  eliminateSum : ∀ {τs ϕ} → Elim Value (#Sum τs) ϕ → Value (#Sum τs) → Thunk ϕ
  eliminateSum (elimSum (f ∷ fs)) (construct (intrSum (here v))) = (f ∷ v ∷ ε) & compile (#apply (var $0) (var $1))
  eliminateSum (elimSum (f ∷ fs)) (construct (intrSum (there vᵢ))) = eliminateSum (elimSum fs) (construct (intrSum vᵢ))

  eliminateProduct : ∀ {τs ϕ} → Elim Value (#Product τs) ϕ → Value (#Product τs) → Thunk ϕ
  eliminateProduct (elimProduct i) (construct (intrProduct vs)) = (get vs i ∷ ε) & compile (var $0)

  eliminateNat' : ∀ {ϕ} → Elim Value #Nat ϕ → Value #Nat → Thunk ϕ
  eliminateNat' (elimNat f) (construct (intrNat v)) =
      (v ∷ f ∷ ε) & compile (#apply (#compose (#mapMaybe (#elimNat (var $1))) (var $1)) (var $0))

  eliminateConat' : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat' elimConat (construct (intrConat (ρ ,, v , f))) =
      (v ∷ f ∷ ε) & compile (#apply (#compose (var $1) (#mapMaybe (#buildConat (var $1)))) (var $0))

  eliminateStream' : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream' elimStream (construct (intrStream (ρ ,, v , f))) =
      (v ∷ f ∷ ε) & compile (#apply (#compose (var $1) (#mapPair (#buildStream (var $1)))) (var $0))

  eliminateNat : ∀ {ϕ} → Elim Value #Nat ϕ → Value #Nat → Thunk ϕ
  eliminateNat (elimNat f) (construct (intrNat v)) =
      (v ∷ f ∷ ε) &
      ( intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
      ▸ intr (intrArrow (elim $0 (elimNat $3) ▸ pure (intr (intrSum (there (here $0))))))
      ▸ elim $2 (elimSum ($1 ∷ $0 ∷ ε))
      ▸ pure (elim $4 (elimArrow $0))
      )

  eliminateConat'' : ∀ {ϕ} → Elim Value #Conat ϕ → Value #Conat → Thunk ϕ
  eliminateConat'' elimConat (construct (intrConat (ρ ,, v , f))) =
      (v ∷ f ∷ ε) &
      ( elim $1 (elimArrow $0)
      ▸ intr (intrArrow (intr (intrProduct ε) ▸ pure (intr (intrSum (here $0)))))
      ▸ intr (intrArrow (intr (intrConat (ρ ,, $0 , $4)) ▸ pure (intr (intrSum (there (here $0))))))
      ▸ pure (elim $2 (elimSum ($1 ∷ $0 ∷ ε)))
      )

  eliminateConat = eliminateConat''

  eliminateStream : ∀ {τ ϕ} → Elim Value (#Stream τ) ϕ → Value (#Stream τ) → Thunk ϕ
  eliminateStream elimStream (construct (intrStream (ρ ,, v , f))) =
      (v ∷ f ∷ ε) &
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

-- operational semantics
module _ where
  -- Given an environment, transforms compile-time introduction rule into a run-time introduction rule
  plugEnvIntr : ∀ {Γ τ} → Env Γ → Intr (AbsTermM Γ) (Has Γ) τ → Intr Closure Value τ
  plugEnvIntr env rule = mapIntr (\term → env & term) (\x → get env x) rule

  -- Given an environment, transforms compile-time elimination rule into a run-time elimination rule
  plugEnvElim : ∀ {Γ τ ϕ} → Env Γ → Elim (Has Γ) τ ϕ → Elim Value τ ϕ
  plugEnvElim env rule = mapElim (\x → get env x) rule

  -- Performs a single computation step
  reduce : ∀ {τ} → Machine τ → Step τ
  reduce ((env & return x) ▹ stack) = composeValueStack (get env x) stack
  reduce ((env & (intr rule ▸ term')) ▹ stack) = continue (((value ∷ env) & term') ▹ stack)
    where
      value : Value _
      value = construct (plugEnvIntr env rule)
  reduce ((env & (elim x rule ▸ term')) ▹ stack) = continue (thunk ▹ ((env & term') ∷ stack))
    where
      thunk : Thunk _
      thunk = eliminate (plugEnvElim env rule) (get env x)

-- locality lemma
module _ where
  -- We can either perform reduction step first, and then compose the result with a stack, or
  -- append the stack first, and then perform reduction.
  locality-lem :
      ∀ {σ τ} → (machine : Machine σ) → (stack : CallStack σ τ)
      → composeStepStack (reduce machine) stack ≡ reduce (composeMachineStack machine stack)
  locality-lem ((env & return x)             ▹ ε)                 stack' = refl
  locality-lem ((env & return x)             ▹ (closure ∷ stack)) stack' = refl
  locality-lem ((env & (intr rule   ▸ term)) ▹ stack)             stack' = refl
  locality-lem ((env & (elim x rule ▸ term)) ▹ stack)             stack' = refl

-- computation trace
module _ where
  data TraceStep {τ} (P : Value τ → Set) : Step τ → Set where
    !finish   : {value : Value τ} → P value → TraceStep P (finish value)
    !continue : {machine : Machine τ} → TraceStep P (reduce machine) → TraceStep P (continue machine)

  data TraceMachine {τ} (P : Value τ → Set) : Machine τ → Set where
    !continueM : {machine : Machine τ} → TraceStep P (reduce machine) → TraceMachine P machine

  TraceThunk : ∀ {τ} → (P : Value τ → Set) → Thunk τ → Set
  TraceThunk P thunk = TraceMachine P (thunk ▹ ε)

  -- returns final value for TraceStep
  resultStep : ∀ {τ P} → {step : Step τ} → TraceStep P step → Value τ
  resultStep {step = finish value}     (!finish _)  = value
  resultStep {step = continue machine} (!continue trace) = resultStep trace

  -- returns final value for TraceMachine
  result : ∀ {τ P} → {machine : Machine τ} → TraceMachine P machine → Value τ
  result (!continueM trace) = resultStep trace

-- examples of values
module _ where
  apply : ∀ {τ ϕ} → Value (τ ⇒ ϕ) → Value τ → Thunk ϕ
  apply f v = eliminateArrow (elimArrow v) f

  ^here : ∀ {τ τs} → Value τ → Value (#Sum (τ ∷ τs))
  ^here v = construct (intrSum (here v))

  ^there : ∀ {τ τs} → Value (#Sum τs) → Value (#Sum (τ ∷ τs))
  ^there (construct (intrSum vᵢ)) = construct (intrSum (there vᵢ)) where

  ^nil : Value (#Product ε)
  ^nil = construct (intrProduct ε)

  ^cons : ∀ {τ τs} → Value τ → Value (#Product τs) → Value (#Product (τ ∷ τs))
  ^cons v (construct (intrProduct vs)) = construct (intrProduct (v ∷ vs))

  ^pair : ∀ {σ τ} → Value σ → Value τ → Value (#Pair σ τ)
  ^pair v₁ v₂ = construct (intrProduct (v₁ ∷ v₂ ∷ ε))
  
  ^nothing : ∀ {τ} → Value (#Maybe τ)
  ^nothing = construct (intrSum (here ^nil))

  ^just : ∀ {τ} → Value τ → Value (#Maybe τ)
  ^just v = construct (intrSum (there (here v)))

-- definition of denotation for values
module _ where
  Val : Type → Set₁
  Val τ = Pred (Value τ)

  AllVal : List Type → Set₁
  AllVal τs = All₁ Val τs

  data !Arrow {ρ τ} (!ρ : Val ρ) (!τ : Val τ) (f : Value (ρ ⇒ τ)) : Set where
    !mkArrow : ({v : Value ρ} → !ρ v → TraceThunk !τ (apply f v)) → !Arrow !ρ !τ f

  data !Sum : ∀ {τs} → All₁ Val τs → Value (#Sum τs) → Set where
    !here  : ∀ {τ τs v}  { !τ : Val τ } { !τs : All₁ Val τs } → !τ v        → !Sum (!τ ∷ !τs) (^here v)
    !there : ∀ {τ τs vᵢ} { !τ : Val τ } { !τs : All₁ Val τs } → !Sum !τs vᵢ → !Sum (!τ ∷ !τs) (^there vᵢ)

  data !Product : ∀ {τs} → All₁ Val τs → Value (#Product τs) → Set where
    ε   : !Product ε ^nil
    _∷_ : ∀ {τ τs} {Val-τ : Val τ} {Val-τs : All₁ Val τs} {v : Value τ} {vs : Value (#Product τs)}
        → Val-τ v → !Product Val-τs vs → !Product (Val-τ ∷ Val-τs) (^cons v vs)
  
  data !Pair {σ τ} (!σ : Val σ) (!τ : Val τ) : Value (#Pair σ τ) → Set where
    _,_ : ∀ {v₁ v₂} → !σ v₁ → !τ v₂ → !Pair !σ !τ (^pair v₁ v₂)

  data !Maybe {τ} (Val-τ : Val τ) : Val (#Maybe τ) where
    !nothing : !Maybe Val-τ ^nothing
    !just    : ∀ {v} → Val-τ v → !Maybe Val-τ (^just v)

  data !Nat : Value #Nat → Set where
    !mkNat : ∀ {n} → !Maybe !Nat n → !Nat (construct (intrNat n))

  record !ConatU {ρ} (step : Value (ρ ⇒ #Maybe ρ)) (value : Value ρ) : Set where
    coinductive
    field forceConat : TraceThunk (!Maybe (!ConatU step)) (apply step value)
  open !ConatU public

  !Conat : Val #Conat
  !Conat (construct (intrConat (ρ ,, value , closure))) = !ConatU closure value
  --data !Conat : Value #Conat → Set where
  --  !mkConat : ∀ {ρ v f} → !ConatU f v → !Conat (construct (intrConat (ρ ,, v , f)))

  record !StreamU {τ ρ} (%Denotation-τ : Val τ) (step : Value (ρ ⇒ #Pair τ ρ)) (value : Value ρ) : Set where
    coinductive
    field forceStream : TraceThunk (!Pair %Denotation-τ (!StreamU %Denotation-τ step)) (apply step value)
  open !StreamU public

  !Stream : ∀ {τ} → Val τ → Val (#Stream τ)
  !Stream %Denotation-τ (construct (intrStream (ρ ,, value , closure))) = !StreamU %Denotation-τ closure value

  mutual
    !Value : (τ : Type) → Val τ
    !Value (ρ ⇒ τ)       = !Arrow (!Value ρ) (!Value τ)
    !Value (#Sum τs)     = !Sum (!Values τs)
    !Value (#Product τs) = !Product (!Values τs)
    !Value (#Nat)        = !Nat
    !Value (#Conat)      = !Conat
    !Value (#Stream τ)   = !Stream (!Value τ)

    !Values : (τs : List Type) → AllVal τs
    !Values ε = ε
    !Values (τ ∷ τs) = !Value τ ∷ !Values τs

-- denotation for other things and a couple of combinators
module _ where
  !Step : ∀ τ → Step τ → Set
  !Step τ step = TraceStep (!Value τ) step

  !Machine : ∀ τ → Machine τ → Set
  !Machine τ machine = TraceMachine (!Value τ) machine

  !Thunk : ∀ τ → Thunk τ → Set
  !Thunk τ thunk = !Machine τ (thunk ▹ ε)

  -- A denotation for an environment consists of denotations for each value in the environment
  !Env : ∀ Γ → Env Γ → Set
  !Env Γ env = AllAll !Value env

  !Closure : ∀ ρ τ → (closure : Closure ρ τ) → Set
  !Closure ρ τ closure = ∀ {value} → !Value ρ value → !Thunk τ (composeValueClosure value closure)

  !CallStack : ∀ σ τ → CallStack σ τ → Set
  !CallStack σ τ stack = ∀ {value} → !Value σ value → !Step τ (composeValueStack value stack)

  !AbsTermM : ∀ Γ ρ τ → (term : AbsTermM Γ ρ τ) → Set
  !AbsTermM Γ ρ τ term = ∀ {env} → !Env (ρ ∷ Γ) env → !Machine τ ((env & term) ▹ ε)

  !TermM : ∀ Γ τ → (term : TermM Γ τ) → Set
  !TermM Γ τ term = ∀ {env} → !Env Γ env → !Machine τ ((env & term) ▹ ε)

  -- Given denotations for a step and a callstack, returns denotation for their composition
  !composeStepStack : ∀ {σ τ step stack} → !Step σ step → !CallStack σ τ stack → !Step τ (composeStepStack step stack)
  !composeStepStack {σ} {τ} {finish value}     {stack} (!finish !value)   !stack = !stack !value
  !composeStepStack {σ} {τ} {continue machine} {stack} (!continue !step') !stack =
      !continue (transport (!Step τ) (locality-lem machine stack) (!composeStepStack !step' !stack))

  infix 20 _▹!_
  _▹!_ : ∀ {σ τ thunk stack} → !Thunk σ thunk → !CallStack σ τ stack → !Step τ (reduce (thunk ▹ stack))
  _▹!_ {σ} {τ} {thunk} {stack} (!continueM !step) !stack =
      transport (!Step τ) (locality-lem (thunk ▹ ε) stack) (!composeStepStack !step !stack)

  !apply : ∀ {σ τ f v} → !Value (σ ⇒ τ) f → !Value σ v → !Thunk τ (apply f v)
  !apply (!mkArrow !f) !v = !f !v

  -- Neat aliases for !finish, !continue and !continueM
  infix 10 ◽_ ∗_ ∗ₘ_

  ◽_ : ∀ {τ value} → !Value τ value → !Step τ (finish value)
  ◽_ = !finish

  ∗_ : ∀ {τ machine} → !Step τ (reduce machine) → !Step τ (continue machine)
  ∗_ = !continue

  ∗ₘ_ : ∀ {τ machine} → !Step τ (reduce machine) → !Machine τ machine
  ∗ₘ_ = !continueM

-- denotational semantics for introduction rules
module _ where
  !constructArrow : ∀ {ρ τ rule} → AllIntr !Closure !Value (ρ ⇒ τ) rule → !Value (ρ ⇒ τ) (construct rule)
  !constructArrow (mkAllIntrArrow !closure) = !mkArrow !closure

  !constructSum : ∀ {τs rule} → AllIntr !Closure !Value (#Sum τs) rule → !Value (#Sum τs) (construct rule)
  !constructSum (mkAllIntrSum (here !v)) = !here !v
  !constructSum (mkAllIntrSum (there !vᵢ)) = !there (!constructSum (mkAllIntrSum !vᵢ))

  !constructProduct : ∀ {τs rule} → AllIntr !Closure !Value (#Product τs) rule → !Value (#Product τs) (construct rule)
  !constructProduct (mkAllIntrProduct ε) = ε
  !constructProduct (mkAllIntrProduct (!v ∷ !vs)) = !v ∷ !constructProduct (mkAllIntrProduct !vs)

  !constructNat : ∀ {rule} → AllIntr !Closure !Value #Nat rule → !Value #Nat (construct rule)
  !constructNat (mkAllIntrNat (!here ε)) = !mkNat !nothing
  !constructNat (mkAllIntrNat (!there (!here !v))) = !mkNat (!just !v)

  !constructConatU : ∀ {ρ f v} → !Value (ρ ⇒ #Maybe ρ) f → !Value ρ v → !ConatU f v
  forceConat (!constructConatU {ρ} {f} {v} !f !v) = mapConstructMachine (!apply !f !v) where
    mapConstructMaybe : ∀ {value} → !Value (#Maybe ρ) value → !Maybe (!ConatU f) value
    mapConstructMaybe (!here ε) = !nothing
    mapConstructMaybe (!there (!here !v')) = !just (!constructConatU !f !v')

    mapConstructStep : ∀ {step} → TraceStep (!Value (#Maybe ρ)) step → TraceStep (!Maybe (!ConatU f)) step
    mapConstructStep (!finish !v') = !finish (mapConstructMaybe !v')
    mapConstructStep (!continue trace) = !continue (mapConstructStep trace)

    mapConstructMachine : ∀ {machine} → TraceMachine (!Value (#Maybe ρ)) machine → TraceMachine (!Maybe (!ConatU f)) machine
    mapConstructMachine (!continueM s) = !continueM (mapConstructStep s)

  !constructConat : ∀ {rule} → AllIntr !Closure !Value #Conat rule → !Value #Conat (construct rule)
  !constructConat (mkAllIntrConat (ρ ,, !v , !f)) = !constructConatU !f !v

  !constructStreamU : ∀ {τ ρ f v} → !Value (ρ ⇒ #Pair τ ρ) f → !Value ρ v → !StreamU (!Value τ) f v
  forceStream (!constructStreamU {τ} {ρ} {f} {v} !f !v) = mapConstructMachine (!apply !f !v) where
    mapConstructPair : ∀ {value} → !Value (#Pair τ ρ) value → !Pair (!Value τ) (!StreamU (!Value τ) f) value
    mapConstructPair (!u ∷ !v' ∷ ε) = !u , !constructStreamU !f !v'

    mapConstructStep : ∀ {step} → TraceStep (!Value (#Pair τ ρ)) step → TraceStep (!Pair (!Value τ) (!StreamU (!Value τ) f)) step
    mapConstructStep (!finish !v') = !finish (mapConstructPair !v')
    mapConstructStep (!continue trace) = !continue (mapConstructStep trace)

    mapConstructMachine : ∀ {machine} → TraceMachine (!Value (#Pair τ ρ)) machine → TraceMachine (!Pair (!Value τ) (!StreamU (!Value τ) f)) machine
    mapConstructMachine (!continueM s) = !continueM (mapConstructStep s)

  !constructStream : ∀ {τ rule} → AllIntr !Closure !Value (#Stream τ) rule → !Value (#Stream τ) (construct rule)
  !constructStream {τ} (mkAllIntrStream (ρ ,, !v , !f)) = !constructStreamU !f !v

  !construct : ∀ {τ rule} → AllIntr !Closure !Value τ rule → !Value τ (construct rule)
  !construct {ρ ⇒ τ}       = !constructArrow
  !construct {#Sum τs}     = !constructSum
  !construct {#Product τs} = !constructProduct
  !construct {#Nat}        = !constructNat
  !construct {#Conat}      = !constructConat
  !construct {#Stream τ}   = !constructStream

-- denotational semantics for elimination rules
module _ where
  !eliminateArrow : ∀ {ρ τ ϕ rule value} → AllElim !Value (ρ ⇒ τ) ϕ rule → !Value (ρ ⇒ τ) value → !Thunk ϕ (eliminate rule value)
  !eliminateArrow (mkAllElimArrow !v) (!mkArrow !f) = !f !v

  !eliminateSum : ∀ {τs ϕ rule value} → AllElim !Value (#Sum τs) ϕ rule → !Value (#Sum τs) value → !Thunk ϕ (eliminate rule value)
  !eliminateSum (mkAllElimSum (!f ∷ !fs)) (!here !v) = ∗ₘ ∗ (!apply !f !v) ▹! \ !v' → ∗ ◽ !v'
  !eliminateSum (mkAllElimSum (!f ∷ !fs)) (!there {vᵢ = construct (intrSum _)} !vᵢ) = !eliminateSum (mkAllElimSum !fs) !vᵢ

  !eliminateProduct : ∀ {τs ϕ rule value} → AllElim !Value (#Product τs) ϕ rule → !Value (#Product τs) value → !Thunk ϕ (eliminate rule value)
  !eliminateProduct (mkAllElimProduct (here refl)) (_∷_ {vs = construct (intrProduct _)} !v !vs) = ∗ₘ ◽ !v
  !eliminateProduct (mkAllElimProduct (there i)) (_∷_ {vs = construct (intrProduct _)} !v !vs) = !eliminateProduct (mkAllElimProduct i) !vs

  !eliminateNat : ∀ {ϕ rule value} → AllElim !Value #Nat ϕ rule → !Value #Nat value → !Thunk ϕ (eliminate rule value)
  !eliminateNat (mkAllElimNat !s) (!mkNat !nothing) =
      ∗ₘ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ ∗ (!apply !s (!here ε)) ▹! \ !v' →
      ∗ ◽ !v'
  !eliminateNat (mkAllElimNat !s) (!mkNat (!just !n)) =
      ∗ₘ ∗ ∗ ∗ ∗ ∗ (!eliminateNat (mkAllElimNat !s) !n) ▹! \ !v' →
      ∗ ∗ ∗ ∗ ∗ (!apply !s (!there (!here !v'))) ▹! \ !v'' →
      ∗ ◽ !v''

  -- (v ∷ f ∷ ε) & compile (#apply (#compose (var $1) (#mapMaybe (#buildConat (var $1)))) (var $0))
  --#apply : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  --!#apply : ∀ {Γ σ τ f v} → !Term f → !Term

  !eliminateConat : ∀ {ϕ rule value} → AllElim !Value #Conat ϕ rule → !Value #Conat value → !Thunk ϕ (eliminate rule value)
  !eliminateConat {value = construct (intrConat (ρ ,, v , f))} mkAllElimConat !v' = ∗ₘ ∗ _▹!_ {thunk = eliminateArrow (elimArrow v) f} {!forceConat !v'!} \ !v'' → ∗ ∗ ∗ ∗ {!!}
    where 
      mapConstructMaybe : ∀ {value} → !Value (#Maybe ρ) value → !Maybe (!ConatU _) value
      mapConstructMaybe = {!!}
      --mapConstructMaybe (!here ε) = !nothing
      --mapConstructMaybe (!there (!here !v')) = !just (!constructConat (mkAllIntrConat (ρ ,, !v' , !f)))

      mapConstructStep : ∀ {step} → TraceStep (!Value (#Maybe ρ)) step → TraceStep (!Maybe (!ConatU _)) step
      mapConstructStep (!finish !v') = !finish (mapConstructMaybe !v')
      mapConstructStep (!continue trace) = !continue (mapConstructStep trace)

      mapConstructMachine : ∀ {machine} → TraceMachine (!Maybe (!ConatU _)) machine → TraceMachine (!Value (#Maybe #Conat)) machine
      mapConstructMachine (!continueM s) = {!!}

  !eliminateStream : ∀ {τ ϕ rule value} → AllElim !Value (#Stream τ) ϕ rule → !Value (#Stream τ) value → !Thunk ϕ (eliminate rule value)
  !eliminateStream = {!!}

  !eliminate : ∀ {τ ϕ rule value} → AllElim !Value τ ϕ rule → !Value τ value → !Thunk ϕ (eliminate rule value)
  !eliminate {ρ ⇒ τ}       = !eliminateArrow
  !eliminate {#Sum τs}     = !eliminateSum
  !eliminate {#Product τs} = !eliminateProduct
  !eliminate {#Nat}        = !eliminateNat
  !eliminate {#Conat}      = !eliminateConat
  !eliminate {#Stream τ}   = !eliminateStream

-- denotational semantics
module _ where
  Top : {Ω : Set} → {X : Ω → Set} → (ω : Ω) → X ω → Set
  Top _ _ = ⊤

  !plugEnvIntr :
      ∀ {Γ τ env rule}
      → !Env Γ env → AllIntr (!AbsTermM Γ) Top τ rule → AllIntr !Closure !Value τ (plugEnvIntr env rule)
  !plugEnvIntr {env = env} {rule = rule} !env all-trace =
      mapAllIntr
        (\term → env & term) (!AbsTermM _) !Closure (\ !term !v → !term (!v ∷ !env))
        (\x → get env x) Top !Value (\{τ} {x} _ → get2 !env x)
        _ all-trace

  !plugEnvElim :
      ∀ {Γ τ ϕ env rule}
      → !Env Γ env → AllElim !Value τ ϕ (plugEnvElim env rule)
  !plugEnvElim {env = env} {rule = rule} !env =
      mapAllElim
        (\x → get env x) Top !Value (\{τ} {x} _ → get2 !env x)
        _ (buildAllElim (\_ → tt) rule)

  AllSubterm : (∀ Γ τ → TermM Γ τ → Set) → (∀ Γ τ → TermM Γ τ → Set)
  AllSubterm P _ _ (return x) = ⊤
  AllSubterm P _ _ (intr rule ▸ term) = AllIntr (\ρ τ term → P _ _ term) Top _ rule × AllSubterm P _ _ term
  AllSubterm P _ _ (elim x rule ▸ term) = AllSubterm P _ _ term

  data AllTerm (P : ∀ Γ τ → TermM Γ τ → Set) : ∀ Γ τ → TermM Γ τ → Set where
    allTermReturn : ∀ {Γ τ} → (x : Has Γ τ) → AllTerm P Γ τ (return x)
    allTermIntr : ∀ {Γ σ τ} → {rule : Intr (AbsTermM Γ) (Has Γ) σ} {term : TermM (σ ∷ Γ) τ}
                → AllIntr (\ρ τ → P (ρ ∷ Γ) τ) Top σ rule → AllTerm P (σ ∷ Γ) τ term → AllTerm P Γ τ (intr rule ▸ term)
    allTermElim : ∀ {Γ ρ σ τ} → {rule : Elim (Has Γ) ρ σ} {term : TermM (σ ∷ Γ) τ}
                → (x : Has Γ ρ) → AllElim Top ρ σ rule → AllTerm P Γ τ (elim x rule ▸ term)

  traceMachine' :
    ∀ {Γ τ ϕ} term env stack
    → !Env Γ env → AllSubterm !TermM Γ τ term → !CallStack τ ϕ stack
    → !Step ϕ (reduce ((env & term) ▹ stack))
  traceMachine' (return x) env stack !env all-sub !stack = !stack (get2 !env x)
  traceMachine' (intr rule ▸ cont) env stack !env (this , that) !stack = ∗ traceMachine' cont _ _ (!value ∷ !env) that !stack
    where
      -- !value : !Value _ (construct (plugEnvIntr env rule))
      !value = !construct (!plugEnvIntr !env this)
  traceMachine' (elim x rule ▸ term) env stack !env that !stack = ∗ !thunk ▹! \ !v → ∗ traceMachine' term _ _ (!v ∷ !env) that !stack
    where
      -- !thunk : !Thunk _ (eliminate (plugEnvElim env rule) (get env x))
      !thunk = !eliminate (!plugEnvElim {rule = rule} !env) (get2 !env x)

  mutual
    --allGoodIntr : ∀ {Γ τ} → (rule : IntrM Γ τ) → AllIntr (\ρ τ → TraceTermM {ρ ∷ Γ} {τ}) (\_ _ → ⊤) τ rule
    allGoodIntr : ∀ {Γ τ} → (rule : IntrM Γ τ) → AllIntr (!AbsTermM Γ) (\_ _ → ⊤) τ rule
    --allGoodIntr (intrArrow term)   = mkAllIntrArrow (mkTraceTermM (\{env} good-env → mkTraceMachineF (traceMachine term env ε good-env \good-value → ◽ good-value)))
    allGoodIntr (intrArrow term)   = mkAllIntrArrow (\{env} good-env → !continueM (traceMachine term env ε good-env \good-value → ◽ good-value))
    allGoodIntr (intrSum rule)     = mkAllIntrSum (buildAllAny (\_ → tt) rule)
    allGoodIntr (intrProduct rule) = mkAllIntrProduct (buildAllAll (\_ → tt) rule)
    allGoodIntr (intrNat rule)     = mkAllIntrNat tt
    allGoodIntr (intrConat rule)   = mkAllIntrConat (_ ,, (tt , tt))
    allGoodIntr (intrStream rule)  = mkAllIntrStream (_ ,, (tt , tt))

    traceMachine :
      ∀ {Γ τ ϕ} → (term : TermM Γ τ) → ∀ env stack
      → !Env Γ env → !CallStack τ ϕ stack
      → !Step ϕ (reduce ((env & term) ▹ stack))
    traceMachine (return x) env ε !env !stack = ◽ (get2 !env x)
    traceMachine (return x) env ((env' & term) ∷ stack) !env !stack = !stack (get2 !env x)
    traceMachine (intr rule ▸ cont) env stack !env !stack = ∗ traceMachine cont _ _ (!value ∷ !env) !stack
      where
        !value : !Value _ (construct (plugEnvIntr env rule))
        !value = !construct (!plugEnvIntr !env (allGoodIntr rule))
    traceMachine (elim x rule ▸ term) env stack !env !stack = ∗ !thunk ▹! \ !v → ∗ traceMachine term _ _ (!v ∷ !env) !stack
      where
        !thunk : !Thunk _ (eliminate (plugEnvElim env rule) (get env x))
        !thunk = !eliminate (!plugEnvElim {rule = rule} !env) (get2 !env x)

  denoteValue : ∀ {τ} → (value : Value τ) → !Value τ value
  denoteValue (construct rule) = {!!}

  denoteEnv : ∀ {Γ} → (env : Env Γ) → !Env Γ env
  denoteEnv ε = ε
  denoteEnv (value ∷ env) = denoteValue value ∷ denoteEnv env

  denoteStack : ∀ {ρ τ} → (stack : CallStack ρ τ) → !CallStack ρ τ stack
  denoteStack ε = \ !v → !finish !v
  denoteStack ((env & term) ∷ stack) = \ !v → !continue (traceMachine term _ _ (!v ∷ denoteEnv env) (denoteStack stack))

  run : ∀ {τ} → (machine : Machine τ) → !Machine τ machine
  run ((env & term) ▹ stack) = {!!}

  --run' : ∀ {τ} → (term : TermM ε τ) → !Machine τ ((ε & term) ▹ ε)
  --run' term = !continueM (traceMachine term ε ε ε ◽_)

-- evaluates closed term to a value
evaluate : ∀ {τ} → Term ε τ → Value τ
evaluate term = result (run (load (compile term)))
