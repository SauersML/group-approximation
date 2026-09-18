import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.Definition
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# Corpus hyperlinearity gives the Elek–Szabó normalization, tex 345–348

`simple_kazhdan_sofic_group.tex`, l.345–348:

> It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} and
> hyperlinear~\cite[Theorem~2]{ElekSzabo}, ...

`isHyperlinearElekSzabo_of_isHyperlinear : IsHyperlinear G → IsHyperlinearElekSzabo G`.

Proof route.  Given `F` and `ε`, put `t = min (ε/3) 1` and take a corpus model `M` on `insert 1 F`
with accuracy `t²`; reindex it along `M.carrier ≃ Fin |M.carrier|` (`Norm.lean`).

* Multiplicativity: `‖φ(gh) − φ(g)φ(h)‖₂ = √(hsDistSq …) ≤ √(t²) = t < ε`.
* Separation from `1` (`hsNormSq_map_sub_one_ge`).  The corpus separates `g` from `1`, not from
  the identity matrix, so compare `U_g` with `U_1`:
  - multiplicativity at `(1, 1)` and unitarity of `U_1` give `‖1 − U_1‖₂² ≤ t²`;
  - separation of `g ≠ 1` gives `Re τ(U_g U_1*) ≤ t²/2` (`hsDistSq_of_unitary`);
  - Cauchy–Schwarz (`normSq_normTrace_le_hsNormSq`) gives `|τ(U_g) − τ(U_g U_1*)| ≤ t`;
  - hence `‖U_g − 1‖₂² = 2 − 2 Re τ(U_g) ≥ 2 − t² − 2t ≥ 2 − ε`, and `√2 − ε ≤ ‖U_g − 1‖₂`
    by `sqrt_two_sub_le_sqrt`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace HyperlinearElekSzabo

open Matrix

/-- In a corpus model at accuracy `t²` containing `1`, every nontrivial `g` has
`‖U_g − 1‖₂² ≥ 2 − t² − 2t`. -/
theorem hsNormSq_map_sub_one_ge {G : Type*} [Group G] {F : Finset G} {t : ℝ}
    (M : HyperlinearModel G F (t ^ 2)) (ht0 : 0 ≤ t) (h1 : (1 : G) ∈ F) {g : G} (hg : g ∈ F)
    (hg1 : g ≠ 1) :
    2 - t ^ 2 - 2 * t ≤ hsNormSq M.carrier (M.map g - 1) := by
  have hU1 := M.isUnitary 1
  have hUg := M.isUnitary g
  have ha : hsNormSq M.carrier (1 - M.map 1) ≤ t ^ 2 := by
    have hm := M.multiplicative 1 h1 1 h1
    rw [mul_one (1 : G)] at hm
    have hfac : M.map 1 - M.map 1 * M.map 1 = M.map 1 * (1 - M.map 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    have hm' : hsNormSq M.carrier (M.map 1 * (1 - M.map 1)) ≤ t ^ 2 := by
      rw [← hfac]
      exact hm
    rwa [hsNormSq_mul_left M.carrier hU1 M.nonempty] at hm'
  have hb : (normTrace M.carrier (M.map g * (M.map 1)ᴴ)).re ≤ t ^ 2 / 2 := by
    have hs := M.separated g hg 1 h1 hg1
    rw [hsDistSq_of_unitary M.carrier hUg hU1 M.nonempty] at hs
    linarith
  have hc : hsNormSq M.carrier (M.map g - 1)
      = 2 - 2 * (normTrace M.carrier (M.map g)).re := by
    have h := hsDistSq_of_unitary M.carrier (B := 1) hUg (Submonoid.one_mem _) M.nonempty
    rw [Matrix.conjTranspose_one, Matrix.mul_one] at h
    exact h
  have hd : Complex.normSq (normTrace M.carrier (M.map g)
      - normTrace M.carrier (M.map g * (M.map 1)ᴴ)) ≤ t ^ 2 := by
    rw [← normTrace_sub]
    have hfac : M.map g - M.map g * (M.map 1)ᴴ = M.map g * (1 - M.map 1)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.mul_one]
    calc Complex.normSq (normTrace M.carrier (M.map g - M.map g * (M.map 1)ᴴ))
        ≤ hsNormSq M.carrier (M.map g - M.map g * (M.map 1)ᴴ) :=
          normSq_normTrace_le_hsNormSq _ _
      _ = hsNormSq M.carrier ((1 - M.map 1)ᴴ) := by
          rw [hfac, hsNormSq_mul_left M.carrier hUg M.nonempty]
      _ = hsNormSq M.carrier (1 - M.map 1) := hsNormSq_conjTranspose _ _
      _ ≤ t ^ 2 := ha
  have he : (normTrace M.carrier (M.map g)).re
      - (normTrace M.carrier (M.map g * (M.map 1)ᴴ)).re ≤ t := by
    have hsq : (normTrace M.carrier (M.map g)
        - normTrace M.carrier (M.map g * (M.map 1)ᴴ)).re ^ 2 ≤ t ^ 2 := by
      rw [Complex.normSq_apply] at hd
      nlinarith [mul_self_nonneg (normTrace M.carrier (M.map g)
        - normTrace M.carrier (M.map g * (M.map 1)ᴴ)).im]
    have hle := (abs_le_of_sq_le_sq' hsq ht0).2
    rw [Complex.sub_re] at hle
    exact hle
  rw [hc]
  linarith

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.hsNormSq_map_sub_one_ge

/-- Corpus hyperlinearity implies hyperlinearity in the printed Elek–Szabó normalization. -/
theorem isHyperlinearElekSzabo_of_isHyperlinear {G : Type*} [Group G] (hG : IsHyperlinear G) :
    IsHyperlinearElekSzabo G := by
  classical
  intro F ε hε
  obtain ⟨t, ht0, ht3, ht1⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε / 3 ∧ t ≤ 1 :=
    ⟨min (ε / 3) 1, lt_min (div_pos hε (by norm_num)) one_pos, min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨M⟩ := hG (insert 1 F) (t ^ 2) (pow_pos ht0 2)
  obtain ⟨e⟩ : Nonempty (M.carrier ≃ Fin (Fintype.card M.carrier)) :=
    ⟨Fintype.equivFin _⟩
  refine ⟨Fintype.card M.carrier, fun g ↦ (M.map g).submatrix e.symm e.symm, M.nonempty,
    fun g ↦ submatrix_mem_unitaryGroup M.carrier e (M.isUnitary g), ?_, ?_⟩
  · intro g hg h hh
    have hrw : (M.map (g * h)).submatrix e.symm e.symm
          - (M.map g).submatrix e.symm e.symm * (M.map h).submatrix e.symm e.symm
        = (M.map (g * h) - M.map g * M.map h).submatrix e.symm e.symm := by
      have hmul := congrArg (fun W ↦ (M.map (g * h)).submatrix e.symm e.symm - W)
        (Matrix.submatrix_mul_equiv (M.map g) (M.map h) e.symm e.symm e.symm)
      exact hmul
    show esNorm _ ((M.map (g * h)).submatrix e.symm e.symm
        - (M.map g).submatrix e.symm e.symm * (M.map h).submatrix e.symm e.symm) < ε
    rw [hrw, esNorm_submatrix]
    have hm := M.multiplicative g (Finset.mem_insert_of_mem hg) h (Finset.mem_insert_of_mem hh)
    calc Real.sqrt (hsNormSq M.carrier (M.map (g * h) - M.map g * M.map h))
        ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt hm
      _ = t := Real.sqrt_sq ht0.le
      _ < ε := by linarith
  · intro g hg hg1
    have hrw : (M.map g).submatrix e.symm e.symm - 1
        = (M.map g - 1).submatrix e.symm e.symm := by
      have hone := congrArg (fun W ↦ (M.map g).submatrix e.symm e.symm - W)
        (Matrix.submatrix_one_equiv (α := ℂ) e.symm).symm
      exact hone
    show Real.sqrt 2 - ε ≤ esNorm _ ((M.map g).submatrix e.symm e.symm - 1)
    rw [hrw, esNorm_submatrix]
    have hX := hsNormSq_map_sub_one_ge M ht0.le (Finset.mem_insert_self 1 F)
      (Finset.mem_insert_of_mem hg) hg1
    have htt : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht0.le (sub_nonneg.2 ht1)]
    exact sqrt_two_sub_le_sqrt hε (by linarith)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.isHyperlinearElekSzabo_of_isHyperlinear

end HyperlinearElekSzabo
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
