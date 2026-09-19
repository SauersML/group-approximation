import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.BigOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Lemma 1.2: rows with two zero coordinates (k2-poly, piece F)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Lemma 1.2. Let `v, v'` be columns and
`w` a row with `w v = w v' = 0`, and let `r ≥ 5`. Then some multiple `c w` lies in the span of the
rows that are orthogonal to `v` and `v'` and vanish at two coordinates (`twoZeroSet`). Here `c` is
any value of the determinant `det (p, q)ᵀ (v, v')` for rows `p, q`
(`det_smul_mem_span_twoZero`), e.g. `c = aⁿ` when `(v, v')` is unimodular over `A[1/a]`.

Tulenbaev proves this locally, by Nakayama. The global proof here is explicit, via Cramer's rule:
* the `2 × 2` minors are `Δᵢⱼ = vᵢ v'ⱼ - vⱼ v'ᵢ`, and `∑ᵢⱼ pᵢ qⱼ Δᵢⱼ = det`;
* the row `gᵢⱼₖ = Δᵢⱼ eₖ - Δₖⱼ eᵢ - Δᵢₖ eⱼ` is orthogonal to `v` and `v'`, and is supported on
  `{i, j, k}` (`cramerRow`);
* `Δᵢⱼ w = ∑ₖ wₖ gᵢⱼₖ` (`minor_smul_eq_sum`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TwoZero

open Matrix

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-- The minor `Δᵢⱼ = vᵢ v'ⱼ - vⱼ v'ᵢ`. -/
def minor2 (v v' : I → A) (i j : I) : A :=
  v i * v' j - v j * v' i

/-- The Cramer row `gᵢⱼₖ = Δᵢⱼ eₖ - Δₖⱼ eᵢ - Δᵢₖ eⱼ`. -/
def cramerRow (v v' : I → A) (i j k : I) : I → A :=
  minor2 v v' i j • Pi.single k 1 - minor2 v v' k j • Pi.single i 1 -
    minor2 v v' i k • Pi.single j 1

/-- Rows orthogonal to `v` and `v'` that vanish at two coordinates. -/
def twoZeroSet (v v' : I → A) : Set (I → A) :=
  {u | u ⬝ᵥ v = 0 ∧ u ⬝ᵥ v' = 0 ∧ ∃ l m, l ≠ m ∧ u l = 0 ∧ u m = 0}

theorem cramerRow_dot (v v' x : I → A) (hx : x = v ∨ x = v') (i j k : I) :
    cramerRow v v' i j k ⬝ᵥ x = 0 := by
  rcases hx with rfl | rfl <;>
    (simp only [cramerRow, sub_dotProduct, smul_dotProduct, single_dotProduct, minor2, smul_eq_mul]
     ring)

#audit_axioms cramerRow_dot

omit [Fintype I] in
theorem cramerRow_apply_of_ne (v v' : I → A) {i j k m : I} (hi : m ≠ i) (hj : m ≠ j)
    (hk : m ≠ k) : cramerRow v v' i j k m = 0 := by
  simp only [cramerRow, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hi, hj, hk, if_false,
    smul_zero, sub_zero]

#audit_axioms cramerRow_apply_of_ne

theorem cramerRow_mem (h5 : 5 ≤ Fintype.card I) (v v' : I → A) (i j k : I) :
    cramerRow v v' i j k ∈ twoZeroSet v v' := by
  refine ⟨cramerRow_dot v v' v (Or.inl rfl) i j k, cramerRow_dot v v' v' (Or.inr rfl) i j k, ?_⟩
  have hc : 1 < (Finset.univ \ ({i, j, k} : Finset I)).card := by
    have h1 := Finset.le_card_sdiff ({i, j, k} : Finset I) Finset.univ
    have h2 : ({i, j, k} : Finset I).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_univ] at h1
    omega
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hl hm
  exact ⟨l, m, hlm, cramerRow_apply_of_ne v v' hl.1 hl.2.1 hl.2.2,
    cramerRow_apply_of_ne v v' hm.1 hm.2.1 hm.2.2⟩

#audit_axioms cramerRow_mem

omit [DecidableEq I] in
theorem sum_mul_minor_left (v v' w : I → A) (j : I) :
    ∑ k, w k * minor2 v v' k j = (w ⬝ᵥ v) * v' j - v j * (w ⬝ᵥ v') := by
  simp only [minor2, dotProduct, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

#audit_axioms sum_mul_minor_left

omit [DecidableEq I] in
theorem sum_mul_minor_right (v v' w : I → A) (i : I) :
    ∑ k, w k * minor2 v v' i k = v i * (w ⬝ᵥ v') - (w ⬝ᵥ v) * v' i := by
  simp only [minor2, dotProduct, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

#audit_axioms sum_mul_minor_right

/-- **Cramer's rule**: `Δᵢⱼ w = ∑ₖ wₖ gᵢⱼₖ` for `w ⊥ v, v'`. -/
theorem minor_smul_eq_sum (v v' w : I → A) (hw : w ⬝ᵥ v = 0) (hw' : w ⬝ᵥ v' = 0) (i j : I) :
    minor2 v v' i j • w = ∑ k, w k • cramerRow v v' i j k := by
  have e0 : ∑ k, w k • (Pi.single k (1 : A) : I → A) = w := by
    simp only [← Pi.single_smul', smul_eq_mul, mul_one]
    exact Finset.univ_sum_single w
  have e1 : ∑ k, w k • cramerRow v v' i j k = minor2 v v' i j • ∑ k, w k • Pi.single k 1 -
      (∑ k, w k * minor2 v v' k j) • Pi.single i 1 -
      (∑ k, w k * minor2 v v' i k) • Pi.single j 1 := by
    simp only [cramerRow, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul,
      smul_smul]
    congr 2
    · exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  rw [e1, e0, sum_mul_minor_left, sum_mul_minor_right, hw, hw']
  simp

#audit_axioms minor_smul_eq_sum

theorem minor_smul_mem_span (h5 : 5 ≤ Fintype.card I) (v v' w : I → A) (hw : w ⬝ᵥ v = 0)
    (hw' : w ⬝ᵥ v' = 0) (i j : I) :
    minor2 v v' i j • w ∈ Submodule.span A (twoZeroSet v v') := by
  rw [minor_smul_eq_sum v v' w hw hw']
  exact sum_mem fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (cramerRow_mem h5 v v' i j k))

#audit_axioms minor_smul_mem_span

omit [DecidableEq I] in
theorem sum_minor (v v' p q : I → A) :
    ∑ i, ∑ j, (p i * q j) * minor2 v v' i j =
      (p ⬝ᵥ v) * (q ⬝ᵥ v') - (q ⬝ᵥ v) * (p ⬝ᵥ v') := by
  have h1 : (p ⬝ᵥ v) * (q ⬝ᵥ v') = ∑ i, ∑ j, (p i * q j) * (v i * v' j) := by
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : (q ⬝ᵥ v) * (p ⬝ᵥ v') = ∑ i, ∑ j, (p i * q j) * (v j * v' i) := by
    simp only [dotProduct, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [minor2]; ring

#audit_axioms sum_minor

/-- **Tulenbaev's Lemma 1.2**, global form: `det · w` is a sum of rows orthogonal to `v, v'` with
two zero coordinates, where `det = (p v)(q v') - (q v)(p v')`. -/
theorem det_smul_mem_span_twoZero (h5 : 5 ≤ Fintype.card I) (v v' w p q : I → A)
    (hw : w ⬝ᵥ v = 0) (hw' : w ⬝ᵥ v' = 0) :
    ((p ⬝ᵥ v) * (q ⬝ᵥ v') - (q ⬝ᵥ v) * (p ⬝ᵥ v')) • w ∈ Submodule.span A (twoZeroSet v v') := by
  rw [← sum_minor, Finset.sum_smul]
  refine sum_mem fun i _ => ?_
  rw [Finset.sum_smul]
  refine sum_mem fun j _ => ?_
  rw [mul_smul]
  exact Submodule.smul_mem _ _ (minor_smul_mem_span h5 v v' w hw hw' i j)

#audit_axioms det_smul_mem_span_twoZero

end TwoZero
end K2Found
end BooneHigmanLinear
end GroupApproximation
