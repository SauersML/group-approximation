import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticPatch
import GroupApproximation.BooneHigman.Metabelian.SuslinDilationStatement
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin dilation, analytic half, part 5: the localized Statement

Lane `bh-met-76`.  Target: `SuslinDilationGeneratedStatement` (`SuslinDilationStatement.lean`).

**Isolated Statement.**  `SuslinDilationAnalyticStatement` has the same hypotheses and asks, for
a normalized `τ ∈ SL_N(A[X])` and a maximal ideal `𝔪`, only for some `a ∉ 𝔪` such that the
image of `τ` in `GL_N(A_a[X])` is elementary (`SuslinDilationAnalyticLocallyElementary`).
There is no second variable and no Quillen matrix: this is exactly what local Horrocks over
`A_𝔪[X]` followed by clearing finitely many denominators produces.

* **Reduction** (`suslinDilationGenerated_of_analytic`): for `N ≥ 3`, Suslin's dilation lemma
  (`suslinDilAn_dilation`, `SuslinDilationAnalyticPatch.lean`) applied to `B = A[X]`,
  `S = A_a[X]`, `s = a` and the Quillen matrix `σ = τ(X + Y) τ(X)⁻¹` (which has `σ(Y = 0) = 1`)
  gives `σ(X + a^k Y) τ(X)⁻¹ ∈ E_N(A[X][Y])`, i.e. `a^k ∈ Q(τ)`, and `a^k ∉ 𝔪`
  (`suslinDilAn_quillen_of_map`).  So `τ` is itself one of the generators.
* **Converse** (`suslinDilationAnalyticStatement_of_generated`): generators give `a ∉ 𝔪` with
  `a ∈ Q(τ)` (`suslinDilation_quillen_of_mem_closure`); substituting `Y ↦ -X/a` over `A_a`
  turns `τ(X + aY) τ(X)⁻¹` into `τ(0) τ(X)⁻¹ = τ(X)⁻¹`, so `τ ∈ E_N(A_a[X])`.

**Truth check.**  TRUE, by Suslin's theorem (A. A. Suslin, 1977): for the two coefficient
families and `N ≥ 3`, `SL_N(A[X]) = E_N(A[X])`, so `a = 1` works.

**LOUD: only equivalent.**  Both implications are proved here, so the isolated Statement is
logically EQUIVALENT to `SuslinDilationGeneratedStatement`, not strictly weaker.  What is removed
is the whole analytic half of the dilation principle (the commutator/dilation estimate).  What
remains open is local Horrocks over `A_𝔪[X]` and clearing denominators from `A_𝔪` to some `A_a`;
the local-ring fact `SL_N(R) = E_N(R)` (row reduction) is NOT proved in this lane.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Substitution

variable {A S : Type*} [CommRing A] [CommRing S]

theorem suslinDilAn_constantCoeff_comp_shift (a : A) :
    (Polynomial.constantCoeff (R := Polynomial A)).comp (suslinLocalGlobalShift a) =
      (Polynomial.constantCoeff (R := Polynomial A)).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply]
    rw [suslinLocalGlobalShift_C]
  · simp only [RingHom.comp_apply]
    rw [suslinLocalGlobalShift_X, map_add,
      Polynomial.constantCoeff_apply (Polynomial.C (Polynomial.C a) * Polynomial.X),
      Polynomial.coeff_mul_X_zero, add_zero]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_constantCoeff_comp_shift

theorem suslinDilAn_mapMap_comp_shift (f : A →+* S) (a : A) :
    (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp (suslinLocalGlobalShift a) =
      (suslinLocalGlobalShift (f a)).comp (Polynomial.mapRingHom f) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, suslinLocalGlobalShift_C, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
  · simp only [RingHom.comp_apply, suslinLocalGlobalShift_X, Polynomial.coe_mapRingHom,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_mapMap_comp_shift

theorem suslinDilAn_dilate_C (c : A) :
    suslinDilAnDilate (Polynomial.C c) = suslinLocalGlobalDilate c :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_dilate_C

/-- `Y ↦ -v X` over `S`, where `v` inverts `f(a)`, kills the shift `X ↦ X + aY`. -/
theorem suslinDilAn_eval_comp_shift (f : A →+* S) {a : A} {v : S} (hv : f a * v = 1) :
    (Polynomial.eval₂RingHom (Polynomial.mapRingHom f)
        (Polynomial.C (-v) * Polynomial.X)).comp (suslinLocalGlobalShift a) =
      ((Polynomial.C : S →+* Polynomial S).comp f).comp (Polynomial.constantCoeff (R := A)) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply]
    rw [suslinLocalGlobalShift_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.constantCoeff_apply,
      Polynomial.coeff_C_zero]
  · simp only [RingHom.comp_apply]
    have hC : Polynomial.C (f a) * Polynomial.C v = 1 := by
      rw [← Polynomial.C_mul, hv, Polynomial.C_1]
    rw [Polynomial.constantCoeff_apply, Polynomial.coeff_X_zero, map_zero, map_zero,
      suslinLocalGlobalShift_X, map_add, map_mul, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_mapRingHom,
      Polynomial.map_X, Polynomial.map_C, Polynomial.C_neg]
    linear_combination (-Polynomial.X) * hC

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_eval_comp_shift

theorem suslinDilAn_eval_comp_C (f : A →+* S) (w : Polynomial S) :
    (Polynomial.eval₂RingHom (Polynomial.mapRingHom f) w).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) =
      Polynomial.mapRingHom f :=
  RingHom.ext fun p ↦ by
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_eval_comp_C

theorem suslinDilAn_away_surj (a : A) :
    ∀ c : Localization.Away a, ∃ (t : ℕ) (b : A),
      c * algebraMap A (Localization.Away a) a ^ t = algebraMap A (Localization.Away a) b := by
  intro c
  obtain ⟨⟨b, x⟩, h⟩ := IsLocalization.surj (Submonoid.powers a) c
  obtain ⟨t, ht⟩ := (Submonoid.mem_powers_iff _ _).1 x.2
  refine ⟨t, b, ?_⟩
  rw [← map_pow, ht]
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_away_surj

theorem suslinDilAn_away_ker (a : A) :
    ∀ b : A, algebraMap A (Localization.Away a) b = 0 → ∃ n : ℕ, a ^ n * b = 0 := by
  intro b hb
  obtain ⟨⟨x, hx⟩, h⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) b).1 hb
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
  exact ⟨n, h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_away_ker

end Substitution
