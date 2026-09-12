import GroupApproximation.Analysis.LIXLemmaSixGenerator

/-!
# The padded null-homotopy as a path of sections

`Analysis/LIXLemmaSixGenerator.lean` proves that `paddedPath` is a continuous
family of `4 × 4` unitaries over `Icc 0 1 × S⁴`, running from `genU ⊕ 1` to the
identity.  That is the mathematics of `hdiag`; what is left is to read it in
the algebra where `diagOne` lives, and this file takes the first two steps of
that reading:

* `paddedPath4`, the same family at index type `Fin 4` rather than
  `Fin 3 ⊕ Fin 1`, since `LIX.flattenTwoTwo` speaks `CStarMat 4`;
* `paddedSection`, the family curried into `C(X₀, ·)`, which is where
  `STW59.SectionAlgebra` lives.  `ContinuousMap.curry` is what turns joint
  continuity into continuity in the sup norm, and it is unconditional at this
  pin.

The remaining steps are cs-limit's two identifications and are pure
composition: `sectionMatrixSymmHom` to the matrix side, `unflattenHom` to
`M₂(M₂(−))`, and `unitaryHom_mem_unitaryComponentOne` to move the membership.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The homotopy at index type `Fin 4` -/

/-- `paddedPath` reindexed along `Fin 3 ⊕ Fin 1 ≃ Fin 4`. -/
def paddedPath4 (t : ℝ) (a : EuclideanSpace ℝ (Fin 5)) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (paddedPath t a)

theorem paddedPath4_apply (t : ℝ) (a : EuclideanSpace ℝ (Fin 5)) (i j : Fin 4) :
    paddedPath4 t a i j =
      paddedPath t a (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := rfl

theorem paddedPath4_one (a : EuclideanSpace ℝ (Fin 5)) : paddedPath4 1 a = 1 := by
  rw [paddedPath4, paddedPath_one]
  simp

theorem paddedPath4_conjTranspose_mul_self {a : EuclideanSpace ℝ (Fin 5)}
    (ha : a ∈ STW59.sphereFour) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (paddedPath4 t a)ᴴ * paddedPath4 t a = 1 := by
  have h := paddedPath_conjTranspose_mul_self ha ht0 ht1
  rw [paddedPath4, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, h]
  simp

theorem paddedPath4_mul_conjTranspose {a : EuclideanSpace ℝ (Fin 5)}
    (ha : a ∈ STW59.sphereFour) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    paddedPath4 t a * (paddedPath4 t a)ᴴ = 1 := by
  have h := paddedPath_mul_conjTranspose ha ht0 ht1
  rw [paddedPath4, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, h]
  simp

theorem continuous_paddedPath4 :
    Continuous fun q : ↥(Set.Icc (0 : ℝ) 1) × ↥STW59.sphereFour =>
      paddedPath4 (q.1 : ℝ) (q.2 : EuclideanSpace ℝ (Fin 5)) := by
  refine continuous_matrix fun i j => ?_
  simpa only [paddedPath4_apply] using
    continuous_paddedPath.matrix_elem (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

/-! ## The homotopy over the stage-zero base

`X₀ = S⁴ × Y₀`, and the homotopy ignores the second factor. -/

/-- The homotopy read over `X₀`, jointly in the time and the base point.
Proved directly from `continuous_seamPath` over this parameter space rather
than by composing the `S⁴`-version with a projection: composing across two
different subtype products sends the elaborator into `paddedPath`'s whole
definitional tower and times out. -/
theorem continuous_paddedPath_baseX :
    Continuous fun q : ↥(Set.Icc (0 : ℝ) 1) × STW59.baseX 0 =>
      paddedPath (q.1 : ℝ) ((q.2.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) := by
  have hτ : Continuous fun q : ↥(Set.Icc (0 : ℝ) 1) × STW59.baseX 0 => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hξ : Continuous fun q : ↥(Set.Icc (0 : ℝ) 1) × STW59.baseX 0 =>
      equatorEmb ((q.2.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) :=
    continuous_equatorEmb.comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const continuous_const
  exact continuous_seamPath hτ hξ
    (fun q => isFrameDatum_contractNorth unit_e3
      (isEquator_equatorEmb q.2.1.2) q.1.2.1 q.1.2.2)
    (fun q => isFrameDatum_contractSouth unit_e3
      (isEquator_equatorEmb q.2.1.2) q.1.2.1 q.1.2.2)

theorem continuous_paddedPath4_baseX :
    Continuous fun q : ↥(Set.Icc (0 : ℝ) 1) × STW59.baseX 0 =>
      paddedPath4 (q.1 : ℝ) ((q.2.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) := by
  refine continuous_matrix fun i j => ?_
  simpa only [paddedPath4_apply] using
    continuous_paddedPath_baseX.matrix_elem (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

/-- The homotopy as a continuous map on `I × X₀`, ready for currying. -/
def paddedCM : C(↥(Set.Icc (0 : ℝ) 1) × STW59.baseX 0, Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨fun q => paddedPath4 (q.1 : ℝ) ((q.2.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)),
    continuous_paddedPath4_baseX⟩

/-- **The homotopy as a path of matrices of continuous functions.**
`ContinuousMap.curry` is what turns the joint continuity into continuity in
the topology of `C(X₀, ·)`; it needs no compactness hypothesis at this pin. -/
def paddedSection : C(↥(Set.Icc (0 : ℝ) 1), C(STW59.baseX 0, Matrix (Fin 4) (Fin 4) ℂ)) :=
  paddedCM.curry

@[simp]
theorem paddedSection_apply (t : ↥(Set.Icc (0 : ℝ) 1)) (w : STW59.baseX 0) :
    paddedSection t w
      = paddedPath4 (t : ℝ) ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) := rfl

end

end LIX
end GroupApproximation
