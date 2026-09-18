import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjCol
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjRow
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrix lemmas for pairs of relative conjugates

Lane `bh-met-93e`, matrix module.  Over a ring `R`, with `padMat : St(n, R) → M_n(R)`:

* `k2KarInd_mul_single_mul_apply`: `(G e_ij(a) H)_pq = G_pi a H_jq`;
* `k2KarInd_padMat_ringMap`: `padMat` commutes with coefficient maps, entrywise;
* `k2KarInd_padMat_conj_apply`: the entries of `padMat (g x_ij(a) g⁻¹)`;
* `k2KarInd_row_ne_zero`: `e_j ᵥ* padMat g⁻¹ ≠ 0` (it is a row of an invertible matrix);
* `k2KarInd_vec_dichotomy`: if `R` has no zero divisors, `W ≠ 0` and `V_p W_q = e_kl(-c)_pq`
  for all `p, q`, then either `V = 0 ∧ c = 0`, or `V = V_k e_k`, `W = W_l e_l` and
  `V_k W_l + c = 0`.  (A rank-one matrix equal to `e_kl(-c)` is concentrated on `(k, l)`.)
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix

section KarIndMat

variable {R : Type*} [Ring R] {n : ℕ}

theorem k2KarInd_mul_single_mul_apply (G H : Matrix (Fin n) (Fin n) R) (i j p q : Fin n)
    (a : R) : (G * Matrix.single i j a * H) p q = G p i * a * H j q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j, Matrix.mul_single_apply_same]
  · intro r _ hr
    rw [Matrix.mul_single_apply_of_ne (hbj := hr), zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_mul_single_mul_apply

/-- `padMat` commutes with coefficient maps, entrywise. -/
theorem k2KarInd_padMat_ringMap {S : Type*} [Ring S] (f : R →+* S) (g : St n R) (p q : Fin n) :
    padMat (ringMap f g) p q = f (padMat g p q) := by
  have e := congrArg (fun u : elementaryGroup (Fin n) S =>
    ((u : (Matrix (Fin n) (Fin n) S)ˣ) : Matrix (Fin n) (Fin n) S) p q) (projection_ringMap f g)
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_padMat_ringMap

theorem k2KarInd_mulVec_single_apply (G : Matrix (Fin n) (Fin n) R) (i p : Fin n) (b : R) :
    (G *ᵥ Pi.single i b) p = G p i * b :=
  dotProduct_single (fun r => G p r) b i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_mulVec_single_apply

/-- The entries of `padMat (g x_ij(a) g⁻¹)`. -/
theorem k2KarInd_padMat_conj_apply (g : St n R) (i j : Fin n) (hij : i ≠ j) (a : R)
    (p q : Fin n) :
    padMat (g * x i j hij a * g⁻¹) p q =
      (1 : Matrix (Fin n) (Fin n) R) p q + padMat g p i * a * padMat g⁻¹ j q := by
  have hGH : padMat g * padMat g⁻¹ = 1 := by
    rw [← map_mul padMat g g⁻¹, mul_inv_cancel, map_one]
  rw [map_mul padMat (g * x i j hij a) g⁻¹, map_mul padMat g (x i j hij a), padMat_x, mul_add,
    add_mul, mul_one, hGH, Matrix.add_apply, k2KarInd_mul_single_mul_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_padMat_conj_apply

/-- A row of the invertible matrix `padMat g⁻¹` is nonzero. -/
theorem k2KarInd_row_ne_zero (h10 : (1 : R) ≠ 0) (g : St n R) (j : Fin n) :
    Pi.single j (1 : R) ᵥ* padMat g⁻¹ ≠ 0 := by
  intro h
  have e : Pi.single j (1 : R) ᵥ* padMat g⁻¹ ᵥ* padMat g = Pi.single j 1 := by
    rw [Matrix.vecMul_vecMul, ← map_mul padMat g⁻¹ g, inv_mul_cancel, map_one,
      Matrix.vecMul_one]
  rw [h, Matrix.zero_vecMul] at e
  have e2 := congrFun e j
  rw [Pi.zero_apply, Pi.single_eq_same] at e2
  exact h10 e2.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_row_ne_zero

/-- **Rank-one dichotomy.**  A product `V_p W_q` equal to `e_kl(-c)` (with `W ≠ 0`, no zero
divisors) is either zero with `c = 0`, or concentrated on `(k, l)`. -/
theorem k2KarInd_vec_dichotomy (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) {k l : Fin n}
    {c : R} {V W : Fin n → R} (hW : W ≠ 0)
    (hVW : ∀ p q, V p * W q = Matrix.single k l (-c) p q) :
    (V = 0 ∧ c = 0) ∨
      (V = Pi.single k (V k) ∧ W = Pi.single l (W l) ∧ V k * W l + c = 0) := by
  obtain ⟨q₀, hq₀⟩ := Function.ne_iff.mp hW
  by_cases hc : c = 0
  · refine Or.inl ⟨funext fun p => ?_, hc⟩
    have e := hVW p q₀
    rw [hc, neg_zero, Matrix.single_zero, Matrix.zero_apply] at e
    exact (hR _ _ e).resolve_right hq₀
  · have ekl := hVW k l
    rw [Matrix.single_apply_same] at ekl
    have hVk : V k ≠ 0 := fun h0 => hc (by
      rw [h0, zero_mul] at ekl
      exact neg_eq_zero.mp ekl.symm)
    have hWl : W l ≠ 0 := fun h0 => hc (by
      rw [h0, mul_zero] at ekl
      exact neg_eq_zero.mp ekl.symm)
    refine Or.inr ⟨funext fun p => ?_, funext fun q => ?_, by rw [ekl, neg_add_cancel]⟩
    · by_cases hp : p = k
      · rw [hp, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hp]
        have e := hVW p l
        rw [Matrix.single_apply_of_row_ne (Ne.symm hp)] at e
        exact (hR _ _ e).resolve_right hWl
    · by_cases hq : q = l
      · rw [hq, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hq]
        have e := hVW k q
        rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hq)] at e
        exact (hR _ _ e).resolve_left hVk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_vec_dichotomy

end KarIndMat

end GroupApproximation.BooneHigman.Metabelian.ElemFP
