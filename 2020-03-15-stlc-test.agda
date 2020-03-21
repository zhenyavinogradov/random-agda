{-
module Test where
  infixr 5 _▸_
  _▸_ : ∀ {Γ ρ τ} → Expr Γ ρ → Term (ρ ∷ Γ) τ → Term Γ τ
  _▸_ = set

  num : ∀ Γ → ℕ → Term Γ nat
  num Γ n = set zero (go n) where
    go : {Γ : Context} → ℕ → Term (nat ∷ Γ) nat
    go zero = ret here
    go (succ n) = succ here ▸ go n
  
  add : ∀ Γ → Term (nat ∷ nat ∷ Γ) nat
  add _ =
    foldNat nat $1
        (ret $0)
        ( succ $0 ▸
          ret $0
        )
    ▸ ret here
  
  stepn : {τ : Type} → ℕ → Cont ε τ → Value τ + Cont ε τ
  stepn zero s = inr s
  stepn (succ n) s with step s
  … | inl v = inl v
  … | inr s' = stepn n s'
  
  run : ∀ {τ} → ℕ → Term ε τ → Value τ + Cont ε τ
  run i term = stepn i ((ε & term) ∷ ε)
  
  test : Term ε nat
  test =
    lambda _ _ (num _ 4) ▸
    call _ _ $0 ε ▸
    lambda _ _ (num _ 4) ▸
    call _ _ $0 ε ▸
    lambda (nat ∷ nat ∷ ε) _ (add _) ▸
    call _ _ $0 ($1 ∷ $3 ∷ ε) ▸
    ret $0
  
  _ : {!!}
  _ = {!run 50 test!}
-}
