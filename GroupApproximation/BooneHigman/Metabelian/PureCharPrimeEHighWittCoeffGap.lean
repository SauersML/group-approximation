import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffPhi
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittLinEmbed
import GroupApproximation.Meta.AxiomGuard

/-!
# The coefficient statement from the module side (bh-met-87e, part 5)

**Target.** `EHighWittLinCoeffStatement` (`PureCharPrimeEHighWittLinEmbed.lean:53`).

**Not proved: the target itself.** What is proved is a reduction, `eHighWittCoeff_of_module`, to
`EHighWittCoeffModuleStatement`. The target splits into two sides.

* **Ring side (proved outright).** For every `d` take `L = Frac(𝔽_p[X₁..X_d])` and
  `C = D = ZMod (p²)[X₁..X_d]_(p)`. Then `φ : D →+* W₂(L)` is an injective ring map
  (`eHighWittCoeff_phi_injective`), and `W₂(L)` is a commutative ring whose product is
  `eHighWittLin_mul` (`eHighWittCoeff_commRing`). No Cohen theory, Witt library or perfectness
  of `L` is used.
* **Module side (the gap).** `EHighWittCoeffModuleStatement` asks for some `d`, an injective
  additive `j : M →+ Dⁿ` and `D`-matrices `U q` with `j (q • m) = U q · j m`.

**Simpler `C` rejected.** Taking `C = W₂(L)` and `φ = id` would make the gap an equivalent
restatement of the target, which the brief forbids. So we fix the concrete `D` instead.

**LOUD: not logically weaker.** Both statements are true, so neither is strictly weaker than the
other as a proposition. The gap is strictly smaller in proof content: `L`, `C`, `φ`, injectivity
and multiplicativity are all supplied here. It is pure module theory over one fixed local ring.

**Truth of the gap (paper, Cohen-free).** Let `R = ZMod (p²)[Q]/ann M` and `P̄ = P/ann M`.
1. `R/P̄` is a finitely generated `𝔽_p`-domain (`p ∈ P`). Pick `t₁..t_d ∈ R` whose images form a
   transcendence basis, giving `D₀ = ZMod (p²)[X] → R`. If `a ∈ S` (that is, `a mod p ≠ 0`), then
   the image of `a` in `R/P̄` is nonzero, since `𝔽_p[X] → R/P̄` is injective. So `a` acts
   injectively on `M` (`smul_injective_of_notMem`). Hence `M ↪ S⁻¹M`, a `D`-module.
2. `S⁻¹M` has a filtration by `P^i S⁻¹M` of length `≤ k`. Each factor is a finitely generated
   module over `S⁻¹(R/P̄)`, which is finite over `K = Frac 𝔽_p[X] = D/pD` (a finitely generated
   domain algebraic over a field). So `S⁻¹M` is a finitely generated `D`-module.
3. The ideals of `D` are `0`, `pD` and `D`, and `pD ≅ D/pD`. By Baer's criterion `D` is
   self-injective, so the finitely generated module `S⁻¹M` embeds in some `Dˢ`.
4. Each `q ∈ Q` acts `D`-linearly on `S⁻¹M`. By injectivity of `Dˢ` it extends to a `D`-matrix
   `U q` on `Dˢ`. Set `n = s` and let `j` be `M ↪ S⁻¹M ↪ Dˢ`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Gap (bh-met-87e, module side).** `M` embeds additively into `Dⁿ` with `Q` acting by
`D`-matrices, where `D = ZMod (p²)[X₁..X_d]_(p)` is `eHighWittCoeff_D p (Fin d)`. It is true on
paper (see the module docstring). It is not strictly weaker than `EHighWittLinCoeffStatement`,
but it is strictly smaller in proof content: the ring side is `eHighWittCoeff_phi_injective`. -/
def EHighWittCoeffModuleStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Q : Type) [CommGroup Q], Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ 2)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ 2)) Q) M →
      ∀ (P : Ideal (MonoidAlgebra (ZMod (p ^ 2)) Q)) (k : ℕ),
        Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ 2)) Q) M P k →
        ((p : ℕ) : MonoidAlgebra (ZMod (p ^ 2)) Q) ∈ P →
        2 ≤ k → (∃ m : M, p • m ≠ 0) → Infinite M →
      ∃ (d n : ℕ) (j : M →+ (Fin n → eHighWittCoeff_D p (Fin d)))
        (U : Q → Fin n → Fin n → eHighWittCoeff_D p (Fin d)),
        Function.Injective j ∧
        ∀ (q : Q) (m : M) (i : Fin n),
          j (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m) i = ∑ l, U q i l * j m l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighWittCoeffModuleStatement

/-- **Endpoint (reduction).** The coefficient statement follows from the module side, using
the injective ring map `D →+* W₂(L)`. -/
theorem eHighWittCoeff_of_module (h : EHighWittCoeffModuleStatement) :
    EHighWittLinCoeffStatement := by
  intro p _ Q _ hfg M _ _ hfin P k hM hpP hk hne hinf
  obtain ⟨d, n, j, U, hj, hU⟩ := h p Q hfg M hfin P k hM hpP hk hne hinf
  exact ⟨eHighWittCoeff_L p (Fin d), inferInstance, ringChar.eq _ p,
    eHighWittCoeff_D p (Fin d), inferInstance, (eHighWittCoeff_phi p (Fin d)).toAddMonoidHom,
    eHighWittCoeff_phi_injective p (Fin d),
    fun a b => map_mul (eHighWittCoeff_phi p (Fin d)) a b, n, j, U, hj, hU⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_of_module

/-- **Composite endpoint.** The weight-polynomial Witt embedding follows from the module side. -/
theorem eHighWittCoeff_wittEmbed_of_module (h : EHighWittCoeffModuleStatement) :
    EHighArtinHasseWittEmbedStatement :=
  eHighWittLin_wittEmbed_of_coeff (eHighWittCoeff_of_module h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_wittEmbed_of_module

/-- **Composite endpoint.** The `e = 2` infinite mixed case follows from the module side. -/
theorem eHighWittCoeff_eTwo_of_module (h : EHighWittCoeffModuleStatement) :
    EHighETwoStatement :=
  eHighWittLin_eTwo_of_coeff (eHighWittCoeff_of_module h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_eTwo_of_module

end GroupApproximation.BooneHigman.Metabelian.Coprimary
