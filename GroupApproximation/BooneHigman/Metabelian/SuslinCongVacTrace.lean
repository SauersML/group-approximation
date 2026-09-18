import GroupApproximation.BooneHigman.Metabelian.SuslinCongVacRankOne
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: the trace-adjustment criterion for `SuslinCongLocGen`

Lane `bh-met-92a`.

For `σ = [[a, b], [c, d]] ∈ SL₂(S)`, `tr(σ E₂₁(r)) = a + d + b r` and `tr(σ E₁₂(r)) = a + d + c r`.
Over a GCD domain `S`, trace-2 elements are rank-one unipotents
(`suslinCongVac_rankOne_of_trace`), so

* `suslinCongVac_mem_of_trace_adj21`: `∃ r, a + d + b r = 2` ⟹ `σ ∈ SuslinCongLocGen A S`;
* `suslinCongVac_mem_of_trace_adj12`: `∃ r, a + d + c r = 2` ⟹ `σ ∈ SuslinCongLocGen A S`;
* `suslinCongVac_unip_le`: the normal closure of all trace-2 elements of `SL₂(S)` lies in
  `SuslinCongLocGen A S`;
* `suslinCongVac_mem_of_trace_loc`: the case `S = A_𝔭[X]`, `A` a UFD (`A_𝔭` and `A_𝔭[X]` are
  UFDs by Mathlib instances).  This covers both families `F_p[t₁..t_k]` and
  `ℤ[1/m][t₁..t_k]` (`m ≠ 0`).

In particular a normalized congruence `σ` whose localized image has `b ∣ 2 - a - d` or
`c ∣ 2 - a - d` in `A_𝔪[X]` satisfies the premise `σ_𝔪 ∈ SuslinCongLocGen` — so it is never a
witness for the residual `SuslinCongLocPowStab`.  These are PARTIAL inclusions only: they do not
make the premise of `SuslinCongLocPowStab` contradictory (see `SuslinCongVacStatement`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Right multiplication by `E₂(S)` does not change membership in `SuslinCongLocGen A S`. -/
theorem suslinCongVac_mem_of_mul_mem {A S : Type*} [CommRing A] [CommRing S]
    {σ e : (Matrix (Fin 2) (Fin 2) S)ˣ} (he : e ∈ elementaryGroup (Fin 2) S)
    (hσe : σ * e ∈ SuslinCongLocGen A S) : σ ∈ SuslinCongLocGen A S := by
  have h := (SuslinCongLocGen A S).mul_mem hσe
    ((SuslinCongLocGen A S).inv_mem (suslinCongVac_elem_mem (A := A) he))
  rwa [mul_inv_cancel_right] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_mem_of_mul_mem

/-- The value of `σ · E_{ij}(r)`. -/
theorem suslinCongVac_val_mul_elem {S : Type*} [CommRing S] (σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (i j : Fin 2) (hij : i ≠ j) (r : S) :
    ((σ * elementaryUnit i j hij r : (Matrix (Fin 2) (Fin 2) S)ˣ) :
        Matrix (Fin 2) (Fin 2) S) =
      (σ : Matrix (Fin 2) (Fin 2) S) + (σ : Matrix (Fin 2) (Fin 2) S) * Matrix.single i j r := by
  rw [Units.val_mul]
  change (σ : Matrix (Fin 2) (Fin 2) S) * (1 + Matrix.single i j r) = _
  rw [mul_add, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_val_mul_elem

/-- `det(σ · E_{ij}(r)) = det σ`. -/
theorem suslinCongVac_det_mul_elem {S : Type*} [CommRing S] (σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (i j : Fin 2) (hij : i ≠ j) (r : S) :
    Matrix.det ((σ * elementaryUnit i j hij r : (Matrix (Fin 2) (Fin 2) S)ˣ) :
        Matrix (Fin 2) (Fin 2) S) = Matrix.det (σ : Matrix (Fin 2) (Fin 2) S) := by
  have he : Matrix.det ((elementaryUnit i j hij r : (Matrix (Fin 2) (Fin 2) S)ˣ) :
      Matrix (Fin 2) (Fin 2) S) = 1 := Matrix.det_transvection_of_ne i j hij r
  rw [Units.val_mul, Matrix.det_mul, he, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_det_mul_elem

/-- **Trace adjustment by `E₂₁(r)`**: if `a + d + b r = 2`, then `σ ∈ SuslinCongLocGen A S`. -/
theorem suslinCongVac_mem_of_trace_adj21 {A S : Type*} [CommRing A] [CommRing S] [IsDomain S]
    [IsGCDMonoid S] (σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) S) = 1) (r : S)
    (htr : (σ : Matrix (Fin 2) (Fin 2) S) 0 0 + (σ : Matrix (Fin 2) (Fin 2) S) 1 1 +
      (σ : Matrix (Fin 2) (Fin 2) S) 0 1 * r = 2) :
    σ ∈ SuslinCongLocGen A S := by
  have hne : (1 : Fin 2) ≠ 0 := by decide
  refine suslinCongVac_mem_of_mul_mem (elementaryUnit_mem 1 0 hne r)
    (suslinCongVac_mem_of_trace _ ?_ ?_)
  · rw [suslinCongVac_det_mul_elem, hdet]
  · rw [suslinCongVac_val_mul_elem, Matrix.add_apply, Matrix.add_apply,
      Matrix.mul_single_apply_same,
      Matrix.mul_single_apply_of_ne (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) hne]
    linear_combination htr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_mem_of_trace_adj21

/-- **Trace adjustment by `E₁₂(r)`**: if `a + d + c r = 2`, then `σ ∈ SuslinCongLocGen A S`. -/
theorem suslinCongVac_mem_of_trace_adj12 {A S : Type*} [CommRing A] [CommRing S] [IsDomain S]
    [IsGCDMonoid S] (σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) S) = 1) (r : S)
    (htr : (σ : Matrix (Fin 2) (Fin 2) S) 0 0 + (σ : Matrix (Fin 2) (Fin 2) S) 1 1 +
      (σ : Matrix (Fin 2) (Fin 2) S) 1 0 * r = 2) :
    σ ∈ SuslinCongLocGen A S := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  refine suslinCongVac_mem_of_mul_mem (elementaryUnit_mem 0 1 hne r)
    (suslinCongVac_mem_of_trace _ ?_ ?_)
  · rw [suslinCongVac_det_mul_elem, hdet]
  · rw [suslinCongVac_val_mul_elem, Matrix.add_apply, Matrix.add_apply,
      Matrix.mul_single_apply_of_ne (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) hne,
      Matrix.mul_single_apply_same]
    linear_combination htr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_mem_of_trace_adj12

/-- **The normal closure of the trace-2 elements of `SL₂(S)` lies in `SuslinCongLocGen A S`**
(`S` a GCD domain). -/
theorem suslinCongVac_unip_le {A S : Type*} [CommRing A] [CommRing S] [IsDomain S]
    [IsGCDMonoid S] :
    Subgroup.normalClosure {τ : (Matrix (Fin 2) (Fin 2) S)ˣ |
        Matrix.det (τ : Matrix (Fin 2) (Fin 2) S) = 1 ∧
          (τ : Matrix (Fin 2) (Fin 2) S) 0 0 + (τ : Matrix (Fin 2) (Fin 2) S) 1 1 = 2} ≤
      SuslinCongLocGen A S := by
  haveI : (SuslinCongLocGen A S).Normal := Subgroup.normalClosure_normal
  exact Subgroup.normalClosure_le_normal fun τ hτ ↦ suslinCongVac_mem_of_trace τ hτ.1 hτ.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_unip_le

/-- **The localized case**: over `A_𝔭[X]`, `A` a UFD, trace-2 elements of `SL₂` lie in
`SuslinCongLocGen A A_𝔭[X]`. -/
theorem suslinCongVac_mem_of_trace_loc {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (σ : (Matrix (Fin 2) (Fin 2) (Polynomial (Localization.AtPrime 𝔭)))ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) (Polynomial (Localization.AtPrime 𝔭))) = 1)
    (htr : (σ : Matrix (Fin 2) (Fin 2) (Polynomial (Localization.AtPrime 𝔭))) 0 0 +
      (σ : Matrix (Fin 2) (Fin 2) (Polynomial (Localization.AtPrime 𝔭))) 1 1 = 2) :
    σ ∈ SuslinCongLocGen A (Polynomial (Localization.AtPrime 𝔭)) := by
  haveI : IsDomain (Localization.AtPrime 𝔭) :=
    IsLocalization.isDomain_of_local_atPrime (P := 𝔭) ‹𝔭.IsPrime›
  exact suslinCongVac_mem_of_trace σ hdet htr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_mem_of_trace_loc

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
