import GroupApproximation.BooneHigman.Metabelian.SuslinBase3FamLift
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2 with the family hypothesis at `k + 1`: proved, but CIRCULAR

Lane `bh-met-91p`.  See `SuslinBase3FamLift.lean` for the LOUD circularity analysis.

* `SuslinBase3FamSuccGlobalStatement`: `SuslinBase3GlobalStatement` with the family hypothesis
  `SL_{N'}(Chain _ k) = E_{N'}` replaced by `SL_{N'}(Chain _ (k + 1)) = E_{N'}`.
* `suslinBase3Fam_succGlobal`: it is PROVED, unconditionally.  Via
  `MvPolynomial.finSuccEquiv : Chain _ (k + 1) ≃ (Chain _ k)[X]`, `diag(σ, 1) ∈ SL₃(A[X]) =
  E₃(A[X])`, and `E₃(A[X])` maps into `E₃(A_𝔪[X])`.
* `suslinBase3Fam_global_of_polynomialSuslin`: **the circularity witness**.  The hypothesis of
  the variant is available to a consumer only from `PolynomialSuslinStatement` (all `k`), which is
  the END PRODUCT of the chain that `SuslinBase3GlobalStatement` feeds
  (`polynomialSuslin_of_oneVariable`, whose induction step at `k` must PROVE `SL = E` at
  `k + 1`).  So this is NOT a closure of `SuslinBase3GlobalStatement` for the consumer.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The strengthened-hypothesis variant**: the family hypothesis is taken at `k + 1`.  TRUE and
proved (`suslinBase3Fam_succGlobal`), but its hypothesis is the conclusion of the one-variable
step that the base feeds: CIRCULAR for the consumer. -/
def SuslinBase3FamSuccGlobalStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.CharPPoly p (k + 1)) N') →
        SuslinBase3StabLocal (Chain.CharPPoly p k) 2) ∧
    ∀ (m k : ℕ),
      (∀ N' : ℕ, 3 ≤ N' → SpecialLinearInElementary (Chain.SIntPoly m (k + 1)) N') →
        SuslinBase3StabLocal (Chain.SIntPoly m k) 2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3FamSuccGlobalStatement

/-- **The variant is a theorem**: `SL₃` at `k + 1` is `SL₃(A[X]) = E₃(A[X])`. -/
theorem suslinBase3Fam_succGlobal : SuslinBase3FamSuccGlobalStatement :=
  ⟨fun p _ k _ hA ↦ suslinBase3Fam_stabLocal_of_slPoly
      (specialLinearInElementary_of_ringEquiv
        (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv (hA 3 le_rfl)),
    fun m k hA ↦ suslinBase3Fam_stabLocal_of_slPoly
      (specialLinearInElementary_of_ringEquiv
        (MvPolynomial.finSuccEquiv (Localization.Away (m : ℤ)) k).toRingEquiv (hA 3 le_rfl))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_succGlobal

/-- **The circularity witness (LOUD)**: the `k + 1` route derives the base from
`PolynomialSuslinStatement`, the end product of the chain that the base feeds.  It is NOT a
route to `SuslinBase3GlobalStatement` for the consumer. -/
theorem suslinBase3Fam_global_of_polynomialSuslin (h : PolynomialSuslinStatement) :
    SuslinBase3GlobalStatement :=
  ⟨fun p _ k hk _ ↦ suslinBase3Fam_succGlobal.1 p k hk (fun N' hN' ↦ h.1 p (k + 1) N' hN'),
    fun m k _ ↦ suslinBase3Fam_succGlobal.2 m k (fun N' hN' ↦ h.2 m (k + 1) N' hN')⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Fam_global_of_polynomialSuslin

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
