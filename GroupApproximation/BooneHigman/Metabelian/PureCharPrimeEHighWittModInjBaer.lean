import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModInjLocal
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModIface
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Span.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `D = ZMod (p²)[σ]_(p)` is self-injective (bh-met-87f, part 3)

This proves `EHighWittModSelfInjStatement` (`PureCharPrimeEHighWittModIface.lean`) by Baer's
criterion (`Module.Baer.injective`). By `eHighWittModInj_ideal_trichotomy` an ideal `I` of `D`
is `⊥`, `pD` or `⊤`, and a linear map `g : I → D` extends to `D` in each case:

* `I = ⊥`: take `0`;
* `I = ⊤`: take `r ↦ r · g 1`;
* `I = pD`: `p · g p = g (p²) = 0`, so `g p = p c` (`eHighWittModInj_ann`), and `r ↦ r c`
  agrees with `g` on `a p`, because `g (a p) = a · g p = a p c`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

variable (p : ℕ) (σ : Type)

/-- **Baer's criterion holds for `D` over itself.** -/
theorem eHighWittModInj_baer [Fact p.Prime] :
    Module.Baer (eHighWittCoeff_D p σ) (eHighWittCoeff_D p σ) := by
  intro I g
  rcases eHighWittModInj_ideal_trichotomy p σ I with rfl | rfl | rfl
  · refine ⟨0, fun x mem => ?_⟩
    rw [LinearMap.zero_apply, (Submodule.mk_eq_zero _ mem).mpr ((Submodule.mem_bot _).mp mem),
      map_zero]
  · have hpI : ((p : ℕ) : eHighWittCoeff_D p σ) ∈
        Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)} :=
      Ideal.mem_span_singleton_self _
    have h0 : ((p : ℕ) : eHighWittCoeff_D p σ) •
        (⟨_, hpI⟩ : Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)}) = 0 :=
      Subtype.ext (by
        rw [Submodule.coe_smul, Submodule.coe_mk, smul_eq_mul, Submodule.coe_zero,
          eHighWittModInj_p_mul_p p σ])
    have h1 := map_smul g ((p : ℕ) : eHighWittCoeff_D p σ) ⟨_, hpI⟩
    rw [h0, map_zero, smul_eq_mul] at h1
    obtain ⟨c, hc⟩ := eHighWittModInj_ann p σ h1.symm
    refine ⟨LinearMap.toSpanSingleton _ _ c, fun x mem => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp mem
    have e : (⟨_, mem⟩ : Ideal.span {((p : ℕ) : eHighWittCoeff_D p σ)}) =
        a • ⟨_, hpI⟩ :=
      Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_mk, Submodule.coe_mk, smul_eq_mul])
    rw [LinearMap.toSpanSingleton_apply, e, map_smul, hc, smul_eq_mul, smul_eq_mul, mul_assoc]
  · have h1 : (1 : eHighWittCoeff_D p σ) ∈ (⊤ : Ideal (eHighWittCoeff_D p σ)) :=
      Submodule.mem_top
    refine ⟨LinearMap.toSpanSingleton _ _ (g ⟨1, h1⟩), fun x mem => ?_⟩
    have e : (⟨x, mem⟩ : (⊤ : Ideal (eHighWittCoeff_D p σ))) = x • ⟨1, h1⟩ :=
      Subtype.ext (by
        rw [Submodule.coe_smul, Submodule.coe_mk, Submodule.coe_mk, smul_eq_mul, mul_one])
    rw [LinearMap.toSpanSingleton_apply, e]
    exact (map_smul g x _).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_baer

/-- **`D = ZMod (p²)[σ]_(p)` is self-injective.** -/
theorem eHighWittModInj_selfInj [Fact p.Prime] :
    Module.Injective (eHighWittCoeff_D p σ) (eHighWittCoeff_D p σ) :=
  Module.Baer.injective (eHighWittModInj_baer p σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_selfInj

/-- **Endpoint: `EHighWittModSelfInjStatement` holds.** -/
theorem eHighWittModInj_selfInjStatement : EHighWittModSelfInjStatement := by
  intro p _ d
  exact eHighWittModInj_selfInj p (Fin d)

#audit_closed_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_selfInjStatement

end GroupApproximation.BooneHigman.Metabelian.Coprimary
