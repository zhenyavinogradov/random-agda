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
