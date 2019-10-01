-- language for types with abstraction
module _ where

module _ where
  module _ where
    data ⊥ : Set where

    record ⊤ : Set where
      constructor tt

    record _×_ (A B : Set) : Set where
      constructor _,_
      field
        fst : A
        snd : B
    open _×_ public

    data _+_ (A B : Set) : Set where
      inl : A → A + B
      inr : B → A + B

    data Bool : Set where
      false true : Bool
    {-# BUILTIN BOOL Bool #-}
    {-# BUILTIN FALSE false #-}
    {-# BUILTIN TRUE true #-}

    data Maybe (A : Set) : Set where
      nothing : Maybe A
      just : A → Maybe A

    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ
    {-# BUILTIN NATURAL ℕ #-}
  
    infixr 5 _∷_
    data List (A : Set) : Set where
      ε : List A
      _∷_ : A → List A → List A
    {-# BUILTIN LIST List #-}

    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,,_
      field
        π₁ : A
        π₂ : B π₁
    open Σ public

  -- finite
  module _ where
    ⊥-elim : {A : Set} → ⊥ → A
    ⊥-elim ()

    either : {A B X : Set} → (A → X) → (B → X) → (A + B → X)
    either f g (inl a) = f a
    either f g (inr b) = g b

    bimapEither : {A A' B B' : Set} → (A → A') → (B → B') → (A + B → A' + B')
    bimapEither f g (inl a) = inl (f a)
    bimapEither f g (inr b) = inr (g b)

  -- maybe
  module _ where
    maybe : {A B : Set} → B → (A → B) → (Maybe A → B)
    maybe b f nothing = b
    maybe b f (just a) = f a

  -- map
  module _ where
    mapMaybe : ∀ {A B} → (A → B) → (Maybe A → Maybe B)
    mapMaybe f nothing = nothing
    mapMaybe f (just a) = just (f a)

    mapPairLeft : ∀ {E A B} → (A → B) → (A × E → B × E)
    mapPairLeft f (a , b) = (f a , b)

    mapEitherLeft : ∀ {E A B} → (A → B) → (A + E → B + E)
    mapEitherLeft f (inl a) = inl (f a)
    mapEitherLeft f (inr e) = inr e

    mapPairRight : ∀ {E A B} → (A → B) → (E × A → E × B)
    fst (mapPairRight f p) = fst p
    snd (mapPairRight f p) = f (snd p)

    mapArrow : {E A B : Set} → (A → B) → ((E → A) → (E → B))
    (mapArrow f g) x = f (g x)

    mapList : {A B : Set} → (A → B) → (List A → List B)
    mapList f ε = ε
    mapList f (a ∷ as) = f a ∷ mapList f as

  -- function
  module _ where
    identity : {A : Set} → A → A
    identity x = x

    _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
    (f ∘ g) x = f (g x)

    _€_ : {A B : Set} → A → (A → B) → B
    x € f = f x
  
  -- boolean
  module _ where
    or : List Bool → Bool
    or ε = false
    or (false ∷ bs) = or bs
    or (true ∷ bs) = true

    bool : {X : Set} → X → X → (Bool → X)
    bool a b true = a
    bool a b false = b

  -- list
  module _ where
    single : {A : Set} → A → List A
    single a = a ∷ ε

    Nelist : Set → Set
    Nelist A = A × List A

    nelistToList : {A : Set} → Nelist A → List A
    nelistToList (a , as) = a ∷ as

  module _ where
    postulate Char : Set
    {-# BUILTIN CHAR Char #-}

    postulate String : Set
    {-# BUILTIN STRING String #-}

    primitive
      primIsLower    : Char → Bool
      primIsDigit    : Char → Bool
      primIsAlpha    : Char → Bool
      primIsSpace    : Char → Bool
      primIsAscii    : Char → Bool
      primIsLatin1   : Char → Bool
      primIsPrint    : Char → Bool
      primIsHexDigit : Char → Bool
      primToUpper    : Char → Char
      primToLower    : Char → Char
      --primCharToNat  : Char → Nat
      --primNatToChar  : Nat → Char
      primShowChar   : Char → String
      primCharEquality : Char → Char → Bool

    charIsId : Char → Bool
    charIsId c = or (primIsAlpha c ∷ primIsDigit c ∷ ε)

    primitive
      primStringToList   : String → List Char
      primStringFromList : List Char → String
      primStringAppend   : String → String → String
      primStringEquality : String → String → Bool
      primShowString     : String → String

    infixl 10 _++_
    _++_ : String → String → String
    _++_ = primStringAppend


--#######
module _ where
  Var : Set
  Var = String

  Vars : Set
  Vars = List Var

  -- Abs : (Vars → Set) → (Vars → Set)
  -- Abs F vs = Σ Var \v → F (v ∷ vs)

  data Abs (F : Vars → Set) (vs : Vars) : Set where
    mkAbs : (v : Var) → F (v ∷ vs) → Abs F vs

  data In {A : Set} : List A → A → Set where
    here : ∀ {a as} → In (a ∷ as) a
    there : ∀ {a a' as} → In as a → In (a' ∷ as) a

  Elem : {A : Set} → List A → Set
  Elem {A} as = Σ A \a → In as a

  data Type : Vars → Set where
    var : ∀ {vs} → Elem vs → Type vs
    σ π : ∀ {vs} → List (Type vs) → Type vs
    μ ν : ∀ {vs} → Abs Type vs → Type vs

  record Parser (A : Set) : Set where
    coinductive
    constructor mkParser
    field runParser : String → Maybe ((A + Parser A) × String)
  open Parser public

  -- DelayT M A = νX. M (A + X)
  -- StateT M S A = S → M (A × S)

  pure : ∀ {A} → A → Parser A
  runParser (pure a) = \s → just (inl a , s)

  {-# TERMINATING #-}
  mapParser : ∀ {A B} → (A → B) → Parser A → Parser B
  runParser (mapParser f p) = mapArrow (mapMaybe (mapPairLeft (bimapEither f (mapParser f)))) (runParser p)

  bindMaybe : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
  bindMaybe nothing f = nothing
  bindMaybe (just a) f = f a

  {-# TERMINATING #-}
  bindParser : ∀ {A B} → Parser A → (A → Parser B) → Parser B
  runParser (bindParser p f) s = runParser p s € \r → bindMaybe r \{(c , s') → either (\a → runParser (f a) s' ) (\p' → runParser (bindParser p' f) s') c}

  concatParser : ∀ {A B} → Parser A → Parser B → Parser B
  concatParser p1 p2 = bindParser p1 (\_ → p2)

  topParser : Parser ⊤
  topParser = pure tt

  emptyParser : Parser ⊥
  runParser emptyParser s = nothing

  emptyParser_ : ∀ {A} → Parser A
  runParser emptyParser_ s = nothing

  orMaybe : ∀ {A B} → Maybe A → Maybe B → Maybe (A + B)
  orMaybe (just a) _ = just (inl a)
  orMaybe nothing (just b) = just (inr b)
  orMaybe nothing nothing = nothing

  {-
  {-# TERMINATING #-}
  orParser : ∀ {A B} → Parser A → Parser B → Parser (A + B)
  --runParser (orParser p q) s = mapMaybe (either (mapPairLeft inl) (mapPairLeft inr)) (orMaybe (runParser p s) (runParser q s))
  runParser (orParser p q) s = runParser p s € either {!!} \p' → runParser (orParser p' q) s
  -}

  delay : ∀ {A} → Parser A → Parser A
  runParser (delay p) s = just (inr p , s)

  {-# TERMINATING #-}
  orParser# : ∀ {A} → Parser A → Parser A → Parser A
  -- orParser# p q = mapParser (either identity identity) (orParser p q)
  runParser (orParser# p q) s = runParser p s € maybe (runParser q s) \{(r , s') → either (\a → just (inl a , s')) (\p' → runParser (delay (orParser# p' q)) s') r }

  orParsers : ∀ {A} → List (Parser A) → Parser A
  orParsers ε = mapParser ⊥-elim emptyParser
  orParsers (p ∷ ps) = orParser# p (orParsers ps)

  infixr 5 _>>=_
  _>>=_ : ∀ {A B} → Parser A → (A → Parser B) → Parser B
  _>>=_ = bindParser

  infixr 5 _>>_
  _>>_ : ∀ {A B} → Parser A → Parser B → Parser B
  _>>_ = concatParser

  infixr 6 _<*_
  _<*_ : ∀ {A B} → Parser A → Parser B → Parser A
  p <* q = p >>= \a → q >> pure a

  infixr 5 _<|>_
  _<|>_ : ∀ {A} → Parser A → Parser A → Parser A
  _<|>_ = orParser#

  pred : (Char → Bool) → Parser Char
  runParser (pred p) s = primStringToList s € \{ ε → nothing ; (c ∷ cs) → p c € \{ true → (just (inl c , primStringFromList cs)) ; false → nothing } }

  eatPrefix : List Char → List Char → Maybe (List Char)
  eatPrefix ε s = just s
  eatPrefix (x ∷ p) ε = nothing
  eatPrefix (p ∷ ps) (s ∷ ss) = primCharEquality p s € \{ true → eatPrefix ps ss ; false → nothing }

  string : String → Parser ⊤
  runParser (string p) s = mapMaybe (\cs → inl tt , primStringFromList cs) (eatPrefix (primStringToList p) (primStringToList s))

  {-# TERMINATING #-}
  mutual
    many : ∀ {A} → Parser A → Parser (List A)
    many p = orParser# (mapParser nelistToList (delay (some p))) (pure ε)

    some : ∀ {A} → Parser A → Parser (Nelist A)
    some p = p >>= \a → delay (many p) >>= \as → pure (a , as)

  {-# TERMINATING #-}
  manySepBy : ∀ {A S} → Parser A → Parser S → Parser (List A)
  manySepBy p s = (p >>= \a → many (s >> p) >>= \as → pure (a ∷ as)) <|> pure ε
  --manySepBy p s = (p >>= \a → many (s >> p) >>= \as → pure (a ∷ as))
  --manySepBy p s = (p >>= \a → s >> delay (manySepBy p s) >>= \as → pure (a ∷ as)) <|> pure ε

  parseVar : Parser Var
  parseVar = mapParser (primStringFromList ∘ nelistToList) (some (pred charIsId))

  postulate
    #trust# : {A : Set} → A

  find : (v : Var) → (vs : Vars) → Maybe (In vs v)
  find v ε = nothing
  find v (v' ∷ vs) = bool (just #trust#) (mapMaybe there (find v vs)) (primStringEquality v v')

  parseElemVar : (vs : Vars) → Parser (Elem vs)
  parseElemVar vs = bindParser parseVar \v → maybe emptyParser_ (\i → pure (v ,, i)) (find v vs)

  ws* ws+ : Parser ⊤
  ws* = mapParser (\_ → tt) (many (string " "))
  ws+ = mapParser (\_ → tt) (some (string " "))

  {-# TERMINATING #-}
  parseType : (vs : Vars) → Parser (Type vs)
  parseType vs = orParsers (pμ ∷ pν ∷ pσ ∷ pπ ∷ pvar ∷ ε)
  --parseType vs = orParsers (pμ ∷ pν ∷ pσ ∷ pπ ∷ ε)
  --parseType vs = pvar
    where
      pμ = string "μ" >> ws* >> parseVar >>= \(v : Var) → ws* >> (string ".") >> ws* >> mapParser (\t → μ (mkAbs v t)) (delay (parseType (v ∷ vs)))
      pν = string "ν" >> ws* >> parseVar >>= \(v : Var) → ws* >> (string ".") >> ws* >> mapParser (\t → ν (mkAbs v t)) (delay (parseType (v ∷ vs)))
      pσ = string "σ[" >> ws* >> manySepBy (delay (parseType vs)) (ws* >> string "," >> ws*) >>= \r → ws* >> string "]" >> pure (σ r)
      pπ = string "π[" >> ws* >> manySepBy (delay (parseType vs)) (ws* >> string "," >> ws*) >>= \r → ws* >> string "]" >> pure (π r)
      pvar = mapParser var (parseElemVar vs)

  {-
  List A:
  - "[" · someSepBy A (w* · "," · w*ᵖ) · "]"

  Type vs:
  - "μ" · (v : Var) · "." · " "? · Type (v ∷ vs)
  - "ν" · (v : Var) · "." · " "? · Type (v ∷ vs)
  - "σ" · "[" · List (Type vs) · "]"
  - "π" · "[" · List (Type vs) · "]"
  - elem vs
  -}

  parse : ∀ {A} → ℕ → Parser A → String → Maybe (Maybe (A × String))
  parse zero p s = nothing
  parse (succ n) p s = maybe (just nothing) (\{(r , s) → either (\a → just (just (a , s))) (\p' → parse n p' s ) r }) (runParser p s)

  _ : {!!}
  --_ = {!runParser (parseType vs) s!}
  _ = {!parse 3 (parseType vs) "νX. σ[μY. σ[π[], π[A,Y]], X]"!}
    where
      vs : Vars
      vs = "A" ∷ "B" ∷ ε

  intercalate : String → List String → String
  intercalate d ε = ""
  intercalate d (s ∷ ε) = s
  intercalate d (s ∷ ss@(_ ∷ _)) = s ++ d ++ intercalate d ss

  showVar : Var → String
  showVar x = x

  {-# TERMINATING #-}
  showType : (vs : Vars) → Type vs → String
  showType vs (var (x ,, _)) = showVar x
  showType vs (σ ts) = "σ[" ++ intercalate ("," ++ " ") (mapList (showType vs) ts) ++ "]"
  showType vs (π ts) = "π[" ++ intercalate ("," ++ " ") (mapList (showType vs) ts) ++ "]"
  showType vs (μ (mkAbs v t)) = "μ" ++ showVar v ++ "." ++ " " ++ showType (v ∷ vs) t 
  showType vs (ν (mkAbs v t)) = "ν" ++ showVar v ++ "." ++ " " ++ showType (v ∷ vs) t 

  module test where
    _ : {!!}
    _ = {! showType vs type !}
      where
        vs : Vars
        vs = "A" ∷ ε

        A : Elem vs
        A = "A" ,, here

        !_ : {v : Var} {vs : Vars} → Elem vs → Elem (v ∷ vs)
        !_ (x ,, i) = x ,, there i

        type : Type vs
        type = σ (var A ∷ μ (mkAbs "X" (σ (π ε ∷ π (var (! A) ∷ var ("X" ,, here) ∷ ε) ∷ ε))) ∷ ε)
