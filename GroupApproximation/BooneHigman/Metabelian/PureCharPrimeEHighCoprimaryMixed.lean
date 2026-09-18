import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighCoprimaryExpP
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighDevissageStatement
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighDevissage
import GroupApproximation.Meta.AxiomGuard

/-!
# Reducing the coprimary high-exponent gap to its mixed case (bh-met-79)

`EHighDevissageCoprimaryStatement` splits by whether `p • M = 0`.

* If `p • M = 0`, the case is **proved outright** by
  `eHighCoprimary_exists_gl_of_nsmul_eq_zero`: descend to `F_p[Q]`, apply the proved `e = 1`
  theorem, then use the translation trick.
* If `p • M ≠ 0`, the coprimary exponent satisfies `2 ≤ k`
  (`eHighCoprimary_two_le_of_nsmul_ne_zero`).  This is the residual
  `EHighCoprimaryMixedStatement`.

**Truth check.**  The residual is a special case of `EHighDevissageCoprimaryStatement`: it has
the same conclusion under two extra hypotheses.  So it is true exactly when the target is
true, and the target is a case of Wehrfritz's theorem for f.g. metabelian groups of exponent
dividing `p^e`.

**LOUD: the residual is only EQUIVALENT to the target, not strictly weaker in logical
strength.**  The two statements are interderivable.  Target ⇒ residual is plain
instantiation, and residual ⇒ target is `eHighCoprimary_devissage_of_mixed`.  The gain is
entirely in proof content.  The residual only concerns modules that are not killed by `p`,
with coprimary exponent `k ≥ 2`.  The whole exponent-`p` layer, including every
`F_p[Q]`-module, is discharged unconditionally.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Residual gap (mixed coprimary case).**  This is `EHighDevissageCoprimaryStatement` with
the extra hypotheses `2 ≤ k` and `p • M ≠ 0`.  It is interderivable with that statement. -/
def EHighCoprimaryMixedStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, 2 ≤ e → ∀ (Q : Type) [CommGroup Q], Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M →
      ∀ (P : Ideal (MonoidAlgebra (ZMod (p ^ e)) Q)) (k : ℕ),
        Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ e)) Q) M P k →
        ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ∈ P →
        2 ≤ k → (∃ m : M, p • m ≠ 0) →
      ∃ (K : Type) (_ : Field K) (d : ℕ)
        (κ : Multiplicative M →* Matrix.GeneralLinearGroup (Fin d) K)
        (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective κ ∧
          ∀ (q : Q) (m : M),
            κ (Multiplicative.ofAdd (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) =
              ρ q * κ (Multiplicative.ofAdd m) * (ρ q)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighCoprimaryMixedStatement

/-- **Endpoint (reduction).**  The coprimary high-exponent gap follows from its mixed case.
The `p • M = 0` case is proved outright. -/
theorem eHighCoprimary_devissage_of_mixed (h : EHighCoprimaryMixedStatement) :
    EHighDevissageCoprimaryStatement := by
  intro p hp e he Q _ hfg M _ _ hfin P k hM hpP
  by_cases hne : ∃ m : M, p • m ≠ 0
  · exact h p hp e he Q hfg M hfin P k hM hpP
      (eHighCoprimary_two_le_of_nsmul_ne_zero hM hpP hne) hne
  · refine eHighCoprimary_exists_gl_of_nsmul_eq_zero hp e hfg M hfin fun m => ?_
    by_contra hm
    exact hne ⟨m, hm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimary_devissage_of_mixed

/-- **Endpoint (composite).**  The high-exponent module statement follows from the mixed
coprimary case. -/
theorem eHighCoprimary_pureCharPrimeEHighModule_of_mixed (h : EHighCoprimaryMixedStatement) :
    PureCharPrimeEHighModuleStatement :=
  pureCharPrimeEHighModule_of_eHighDevissageCoprimary (eHighCoprimary_devissage_of_mixed h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimary_pureCharPrimeEHighModule_of_mixed

end GroupApproximation.BooneHigman.Metabelian.Coprimary
