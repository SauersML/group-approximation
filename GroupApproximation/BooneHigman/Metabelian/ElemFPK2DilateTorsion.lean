import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDilateMaps
import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion is killed by dilation: polynomial and matrix lemmas

Lane `bh-met-90h`, helper module.  Let `A` be a commutative ring, `s ∈ A`,
`λ : A[X] → A_s[X]` the coefficientwise localization and `μ_c = k2CubeDilate_scale A c`
(`X ↦ c X`).

* `k2Dilate_scale_eq_zero`: if `f(0) = 0` and `λ f = 0`, then `μ_{s^r} f = 0` for all large `r`.
  Each coefficient `f_n` is `s`-torsion, `s^{k_n} f_n = 0`, and `μ_{s^r}` multiplies `f_n` by
  `s^{r n}`.  For `n ≥ 1` and `r ≥ max k_n` this kills `f_n`; `f_0 = 0` by hypothesis.
* `k2Dilate_scale_mapMatrix_eq_one`: the same for a matrix `P` over `A[X]` with `P(0) = 1` and
  `λ P = 1`, applied to the entries of `P - 1`, with one uniform `m`.
* `k2Dilate_eq_one_of_padHom`: identity padding of matrices is injective at `1`.

Everything is ring theory; no Steinberg relation is used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section DilatePoly

variable {A : Type*} [CommRing A]

/-- A coefficient of a polynomial killed by `A[X] → A_s[X]` is `s`-torsion. -/
theorem k2Dilate_exists_pow_mul_coeff_eq_zero (s : A) (f : Polynomial A)
    (hf : Polynomial.map (algebraMap A (Localization.Away s)) f = 0) (n : ℕ) :
    ∃ k : ℕ, s ^ k * f.coeff n = 0 := by
  have h1 : algebraMap A (Localization.Away s) (f.coeff n) = 0 := by
    rw [← Polynomial.coeff_map, hf, Polynomial.coeff_zero]
  obtain ⟨m, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers s) (Localization.Away s) (f.coeff n)).mp h1
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
  exact ⟨k, by rw [hk]; exact hm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_exists_pow_mul_coeff_eq_zero

/-- **Dilation kills torsion.**  If `f(0) = 0` and `f` dies in `A_s[X]`, then `f(s^r X) = 0`
for all large `r`. -/
theorem k2Dilate_scale_eq_zero (s : A) (f : Polynomial A) (h0 : f.coeff 0 = 0)
    (hf : Polynomial.map (algebraMap A (Localization.Away s)) f = 0) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r → k2CubeDilate_scale A (s ^ r) f = 0 := by
  choose k hk using k2Dilate_exists_pow_mul_coeff_eq_zero s f hf
  refine ⟨f.support.sup k, fun r hr ↦ ?_⟩
  rw [Polynomial.as_sum_support_C_mul_X_pow f, map_sum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [map_mul, map_pow, k2CubeDilate_scale_C, k2CubeDilate_scale_X, mul_pow, ← Polynomial.C_pow,
    ← mul_assoc, ← Polynomial.C_mul]
  have hz : f.coeff n * (s ^ r) ^ n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [h0, zero_mul]
    · have hkn : k n ≤ r * n :=
        ((Finset.le_sup hn).trans hr).trans (Nat.le_mul_of_pos_right r hpos)
      rw [← pow_mul, ← Nat.sub_add_cancel hkn, pow_add, mul_comm (f.coeff n), mul_assoc, hk n,
        mul_zero]
  rw [hz, map_zero, zero_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_scale_eq_zero

end DilatePoly

section DilateMatrix

variable {n R T : Type*} [Fintype n] [DecidableEq n] [Ring R] [Ring T]

theorem k2Dilate_map_one_apply (φ : R →+* T) (i j : n) :
    φ ((1 : Matrix n n R) i j) = (1 : Matrix n n T) i j := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_map_one_apply

/-- If `φ P = 1` then `φ` kills every entry of `P - 1`. -/
theorem k2Dilate_map_sub_one_apply (φ : R →+* T) {P : Matrix n n R} (h : φ.mapMatrix P = 1)
    (i j : n) : φ (P i j - (1 : Matrix n n R) i j) = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
  rw [map_sub, h1, k2Dilate_map_one_apply, sub_self]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_map_sub_one_apply

end DilateMatrix

section DilateMatrixScale

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Matrix form.**  If `P(0) = 1` and `P = 1` over `A_s[X]`, then `P(s^m X) = 1` for some `m`. -/
theorem k2Dilate_scale_mapMatrix_eq_one (s : A) (P : Matrix n n (Polynomial A))
    (h0 : (Polynomial.evalRingHom (0 : A)).mapMatrix P = 1)
    (hs : (Polynomial.mapRingHom (algebraMap A (Localization.Away s))).mapMatrix P = 1) :
    ∃ m : ℕ, (k2CubeDilate_scale A (s ^ m)).mapMatrix P = 1 := by
  have hf : ∀ i j : n, ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2CubeDilate_scale A (s ^ r) (P i j - (1 : Matrix n n (Polynomial A)) i j) = 0 := by
    intro i j
    have e0 := k2Dilate_map_sub_one_apply _ h0 i j
    have es := k2Dilate_map_sub_one_apply _ hs i j
    rw [Polynomial.coe_evalRingHom] at e0
    rw [Polynomial.coe_mapRingHom] at es
    exact k2Dilate_scale_eq_zero s _ (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact e0) es
  choose m hm using hf
  refine ⟨Finset.univ.sup fun ij : n × n ↦ m ij.1 ij.2, ?_⟩
  ext i j
  have h1 := hm i j _ (Finset.le_sup (f := fun ij : n × n ↦ m ij.1 ij.2) (Finset.mem_univ (i, j)))
  rw [map_sub, sub_eq_zero, k2Dilate_map_one_apply] at h1
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_scale_mapMatrix_eq_one

end DilateMatrixScale

section DilatePad

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Ring R]

/-- The `(e i, e j)` entry of the padded matrix is `M i j`. -/
theorem k2Dilate_padHom_apply (e : ι ↪ κ) (M : Matrix ι ι R) (i j : ι) :
    ElementaryPadding.padHom e M (e i) (e j) = M i j := by
  have h : ∀ a : ι, (ElementaryPadding.padEquiv e).symm (e a) = Sum.inl a := fun a ↦
    (Equiv.symm_apply_eq _).mpr (ElementaryPadding.padEquiv_inl e a).symm
  rw [ElementaryPadding.padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply, h, h,
    Matrix.fromBlocks_apply₁₁]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_padHom_apply

/-- Identity padding is injective at `1`. -/
theorem k2Dilate_eq_one_of_padHom (e : ι ↪ κ) {M : Matrix ι ι R}
    (h : ElementaryPadding.padHom e M = 1) : M = 1 := by
  ext i j
  have h1 := congrFun (congrFun h (e i)) (e j)
  rw [k2Dilate_padHom_apply] at h1
  rw [h1]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (e.injective.ne hij)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_eq_one_of_padHom

end DilatePad

end GroupApproximation.BooneHigman.Metabelian.ElemFP
