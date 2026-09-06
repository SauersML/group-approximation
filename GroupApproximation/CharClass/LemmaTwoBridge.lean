import GroupApproximation.CharClass.LemmaTwoStatement
import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann

/-!
# Lemma 2 in the `C(M, ℂ)`-matrix vocabulary

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3).

`CharClass/LemmaTwoStatement.lean` states Lemma 2 in the **continuous-field** model, which
is the one the whole `CharClass` layer speaks: a bundle is a continuous
`M → Matrix ι ι ℂ` and an isomorphism is a continuous field of partial isometries.  The
C*-side speaks the **matrix-over-functions** model instead: a bundle is a projection in
`Matrix ι ι C(M, ℂ)` and an isomorphism is `MurrayVonNeumannEquiv` there.

The two models are the same thing, and `STW59.matEval` is the translation.  This file is
the bridge, and it is deliberately independent of the cohomology layer: `cs-clutching` can
consume Lemma 2 in its own vocabulary as soon as Steps A, C and D land, without waiting on
the Künneth or Steenrod machinery.

## Main results

* `toMatC` — a continuous field of matrices, read as a matrix over `C(M, ℂ)`;
  `matEval_toMatC` says the translation is the identity on points.
* `continuousMvNEquiv_of_murrayVonNeumannEquiv` — an equivalence in the matrix model gives
  one in the continuous-field model.  Evaluation at a point is a `*`-homomorphism, so the
  implementer transports verbatim.
* `not_murrayVonNeumannEquiv` — **Lemma 2 in the C*-side vocabulary**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The two models -/

section Bridge

variable {ι : Type*} [Fintype ι] {M : Type*} [TopologicalSpace M]

/-- A continuous field of matrices, read as a matrix with entries in `C(M, ℂ)`. -/
def toMatC (P : M → Matrix ι ι ℂ) (hP : Continuous P) : Matrix ι ι C(M, ℂ) :=
  Matrix.of fun i j => ⟨fun m => P m i j, hP.matrix_elem i j⟩

@[simp]
theorem matEval_toMatC (P : M → Matrix ι ι ℂ) (hP : Continuous P) (m : M) :
    matEval m (toMatC P hP) = P m := rfl

/-- Evaluation of a matrix over `C(M, ℂ)` is continuous in the point. -/
theorem continuous_matEval (A : Matrix ι ι C(M, ℂ)) :
    Continuous fun m => matEval m A :=
  continuous_matrix fun i j => (A i j).continuous

/-- **The bridge.**  Evaluation at a point is multiplicative and star-preserving
(`matEval_mul`, `matEval_conjTranspose`), so the implementer of an equivalence in the
matrix model is, pointwise, the implementer of one in the continuous-field model. -/
theorem continuousMvNEquiv_of_murrayVonNeumannEquiv {P Q : M → Matrix ι ι ℂ}
    (hP : Continuous P) (hQ : Continuous Q)
    (h : MurrayVonNeumannEquiv (toMatC P hP) (toMatC Q hQ)) :
    ContinuousMvNEquiv P Q := by
  obtain ⟨v, hv1, hv2⟩ := h
  refine ⟨fun m => matEval m v, continuous_matEval v, fun m => ?_, fun m => ?_⟩
  · have h1 := congrArg (matEval m) hv1
    rwa [Matrix.star_eq_conjTranspose, matEval_mul, matEval_conjTranspose,
      matEval_toMatC] at h1
  · have h2 := congrArg (matEval m) hv2
    rwa [Matrix.star_eq_conjTranspose, matEval_mul, matEval_conjTranspose,
      matEval_toMatC] at h2

theorem not_murrayVonNeumannEquiv_of_not_continuousMvNEquiv {P Q : M → Matrix ι ι ℂ}
    (hP : Continuous P) (hQ : Continuous Q) (h : ¬ ContinuousMvNEquiv P Q) :
    ¬ MurrayVonNeumannEquiv (toMatC P hP) (toMatC Q hQ) :=
  fun he => h (continuousMvNEquiv_of_murrayVonNeumannEquiv hP hQ he)

end Bridge

/-! ## 2. The two complements are continuous -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

theorem continuous_sProj : Continuous (sProj (dd := dd)) := by
  refine continuous_matrix fun p q => ?_
  match p, q with
  | Sum.inl i, Sum.inl j =>
    have h : Continuous fun m : baseM dd => bVec m i * star (bVec m j) :=
      ((continuous_apply i).comp continuous_bVec).mul
        (continuous_star.comp ((continuous_apply j).comp continuous_bVec))
    simpa [sProj] using h
  | Sum.inl i, Sum.inr j => simpa [sProj] using continuous_const
  | Sum.inr i, Sum.inl j => simpa [sProj] using continuous_const
  | Sum.inr i, Sum.inr j => simpa [sProj] using continuous_const

theorem continuous_eProj : Continuous (eProj (dd := dd)) := continuous_const

theorem continuous_FHmat : Continuous (FHmat (dd := dd)) :=
  continuous_Vmat.sub continuous_sProj

theorem continuous_EHmat : Continuous (EHmat (dd := dd)) :=
  continuous_Vmat.sub continuous_eProj

/-! ## 3. Lemma 2, in the C*-side vocabulary -/

/-- **Lemma 2 for the C*-side.**  Over `M = S⁵ × ∏ⱼ ℂP^{dⱼ}` the projections `F ⊕ H` and
`𝟏² ⊕ H`, as elements of `Matrix (VIdx dd) (VIdx dd) C(M, ℂ)`, are not Murray--von
Neumann equivalent.

The three hypotheses are Steps A, C and D, with the same owners as in
`CharClass/LemmaTwoStatement.lean`; nothing here depends on the cohomology layer beyond
those, so the join with `cs-clutching` is decoupled from its timing. -/
theorem not_murrayVonNeumannEquiv {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → K)
    (stepA : ContinuousMvNEquiv (FHmat (dd := dd)) EHmat → HasStepAUnitary dd)
    (stepC : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      topClass (mappingTorus Vmat G circHoriz circHeight) ≠ 0)
    (stepD : ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      topClass (mappingTorus Vmat G circHoriz circHeight) = 0) :
    ¬ MurrayVonNeumannEquiv (toMatC (FHmat (dd := dd)) continuous_FHmat)
      (toMatC (EHmat (dd := dd)) continuous_EHmat) :=
  not_murrayVonNeumannEquiv_of_not_continuousMvNEquiv continuous_FHmat continuous_EHmat
    (not_continuousMvNEquiv topClass stepA stepC stepD)

end GroupApproximation.CharClass
