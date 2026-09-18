import GroupApproximation.Sofic.HyperlinearScalar
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed Hilbert–Schmidt normalization, tex 345–348

`simple_kazhdan_sofic_group.tex`, l.345–348:

> It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} and
> hyperlinear~\cite[Theorem~2]{ElekSzabo}, and $L(G)$ embeds in $\mathcal R^\omega$ ...

Elek–Szabó (Math. Ann. 332 (2005)) define hyperlinearity with unitaries `U(n)` and the normalized
Hilbert–Schmidt norm `‖A‖₂ = (tr(A* A) / n)^{1/2}`.  This module fixes that norm on `Fin n`
matrices and relates it to the corpus quantity `hsNormSq` (`Sofic/HyperlinearScalar.lean`).

Proof route:

* `esNorm_eq`: `‖A‖₂ = √(hsNormSq (esModel n) A)` from `ofReal_sum_normSq` and
  `Matrix.trace_mul_comm`.
* `hsNormSq_submatrix`, `esNorm_submatrix`, `submatrix_mem_unitaryGroup`: reindexing a corpus
  model along `Y ≃ Fin n` preserves the norm and unitarity (`Equiv.sum_comp`,
  `Matrix.submatrix_mul_equiv`).
* `sqrt_two_sub_le_sqrt`: `2 - ε ≤ X → √2 - ε ≤ √X`, which turns the corpus squared constant
  `2` into the printed constant `√2`.  No tensor amplification is needed, because the corpus
  separation constant is already the maximal one.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace HyperlinearElekSzabo

open Matrix

/-- The finite model on `Fin n`, reducible so that its carrier is `Fin n` for the elaborator. -/
abbrev esModel (n : ℕ) : FiniteModel := ⟨Fin n, inferInstance, inferInstance⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.esModel

theorem card_esModel (n : ℕ) : Fintype.card (esModel n) = n :=
  Fintype.card_fin n

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.card_esModel

/-- The printed normalized Hilbert–Schmidt norm `‖A‖₂ = (tr(A* A) / n)^{1/2}`. -/
noncomputable def esNorm (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt ((Matrix.trace (Aᴴ * A)).re / n)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.esNorm

/-- The printed trace formula is the corpus normalized squared norm. -/
theorem trace_re_div_eq_hsNormSq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (Aᴴ * A)).re / n = hsNormSq (esModel n) A := by
  have hre : (Matrix.trace (Aᴴ * A)).re
      = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j) := by
    have hsum := ofReal_sum_normSq (esModel n) A
    have htr : Matrix.trace (Aᴴ * A) = Matrix.trace (A * Aᴴ) := Matrix.trace_mul_comm _ _
    rw [htr]
    exact (congrArg Complex.re hsum).symm.trans (Complex.ofReal_re _)
  show _ = (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j)) / (Fintype.card (Fin n) : ℝ)
  rw [hre, Fintype.card_fin]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.trace_re_div_eq_hsNormSq

theorem esNorm_eq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    esNorm n A = Real.sqrt (hsNormSq (esModel n) A) := by
  rw [esNorm, trace_re_div_eq_hsNormSq]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.esNorm_eq

/-- Reindexing along an equivalence does not move the normalized squared norm. -/
theorem hsNormSq_submatrix (Y : FiniteModel) {n : ℕ} (e : Y ≃ Fin n) (A : Matrix Y Y ℂ) :
    hsNormSq (esModel n) (A.submatrix e.symm e.symm) = hsNormSq Y A := by
  have hnum : (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A (e.symm i) (e.symm j)))
      = ∑ x : Y, ∑ y : Y, Complex.normSq (A x y) := by
    calc (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A (e.symm i) (e.symm j)))
        = ∑ i : Fin n, ∑ y : Y, Complex.normSq (A (e.symm i) y) :=
          Finset.sum_congr rfl fun i _ ↦
            Equiv.sum_comp e.symm (fun y ↦ Complex.normSq (A (e.symm i) y))
      _ = ∑ x : Y, ∑ y : Y, Complex.normSq (A x y) :=
          Equiv.sum_comp e.symm (fun x ↦ ∑ y : Y, Complex.normSq (A x y))
  have hcard : (Fintype.card (Fin n) : ℝ) = (Fintype.card Y : ℝ) := by
    exact_mod_cast (Fintype.card_congr e).symm
  show (∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A (e.symm i) (e.symm j)))
      / (Fintype.card (Fin n) : ℝ) = hsNormSq Y A
  rw [hnum, hcard, hsNormSq]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.hsNormSq_submatrix

theorem esNorm_submatrix (Y : FiniteModel) {n : ℕ} (e : Y ≃ Fin n) (A : Matrix Y Y ℂ) :
    esNorm n (A.submatrix e.symm e.symm) = Real.sqrt (hsNormSq Y A) := by
  rw [esNorm_eq, hsNormSq_submatrix]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.esNorm_submatrix

/-- Reindexing along an equivalence preserves unitarity. -/
theorem submatrix_mem_unitaryGroup (Y : FiniteModel) {n : ℕ} (e : Y ≃ Fin n)
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    A.submatrix e.symm e.symm ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hAA : Aᴴ * A = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hAA,
    Matrix.submatrix_one_equiv]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.submatrix_mem_unitaryGroup

/-- The squared constant `2` gives the printed constant `√2`. -/
theorem sqrt_two_sub_le_sqrt {ε X : ℝ} (hε : 0 < ε) (hX : 2 - ε ≤ X) :
    Real.sqrt 2 - ε ≤ Real.sqrt X := by
  by_cases hpos : 0 < Real.sqrt 2 - ε
  · rw [Real.le_sqrt' hpos]
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [mul_pos hε hpos, mul_nonneg hε.le (sub_nonneg.2 Real.one_lt_sqrt_two.le)]
  · exact le_trans (not_lt.1 hpos) (Real.sqrt_nonneg X)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.sqrt_two_sub_le_sqrt

end HyperlinearElekSzabo
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
