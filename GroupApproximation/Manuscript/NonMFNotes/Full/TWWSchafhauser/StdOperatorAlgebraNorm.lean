import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtRing

/-!
# The operator norm on `𝓛(H_J)`

Lane `TWWSch3d3-2C`, work order `WO-3d3-2C`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through the Busby picture of `Ext(S, J)` used in
Schafhauser's proof of the Tikuisis--White--Winter theorem.

`StdBdd J` (from `ObstructionSplitExtRing`) is the `⋆`-algebra of bounded adjointable operators on
the standard module `H_J = standardModule ℕ J`. This file equips it with the operator norm
`‖T‖ = T.opNorm` and proves the normed-ring, normed-algebra and C⋆-identity axioms (Lance,
*Hilbert C⋆-modules*, Ch. 1--2):

* `StdBdd.instNormedAddCommGroup`: a normed group, built from `NormedSpace.Core`;
* `StdBdd.instNormedRing`: submultiplicativity, from `Adjointable.opNorm_comp_le`;
* `StdBdd.instNormedAlgebra`: `‖c • T‖ ≤ ‖c‖ ‖T‖`;
* `StdBdd.instCStarRing`: `‖T‖² ≤ ‖T⋆T‖`, from `Adjointable.opNorm_adjoint_comp_self`.

Completeness is proved in `StdOperatorAlgebraComplete`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The operator norm on `𝓛(H_J)` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`;
Lance Ch. 1). -/
instance StdBdd.instNorm : Norm (StdBdd J) := ⟨fun T => T.1.opNorm⟩

/-- The norm is the operator norm (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.norm_def (T : StdBdd J) : ‖T‖ = T.1.opNorm := rfl

/-- An element of `StdBdd J` is bounded (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.isBounded (T : StdBdd J) : T.1.IsBounded := mem_boundedAdj.mp T.2

/-- Addition is operator addition (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.coe_add (T U : StdBdd J) : (T + U).1 = T.1.add U.1 := rfl

/-- Multiplication is composition (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.coe_mul (T U : StdBdd J) : (T * U).1 = T.1.comp U.1 := rfl

/-- Subtraction is operator subtraction (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.coe_sub (T U : StdBdd J) : (T - U).1 = T.1.sub U.1 := rfl

/-- Scalars act pointwise (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.coe_smul (c : ℂ) (T : StdBdd J) : (c • T).1 = Adjointable.smul c T.1 := rfl

/-- The involution is the adjoint (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.coe_star (T : StdBdd J) : (star T).1 = Adjointable.adjoint T.1 := rfl

/-- Zero is the zero operator (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.coe_zero : (0 : StdBdd J).1 = Adjointable.zero _ _ := rfl

/-- The pointwise operator bound by the norm (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.norm_apply_le (T : StdBdd J) (x : (standardModule ℕ J).carrier) :
    (standardModule ℕ J).norm (T.1.toFun x) ≤ ‖T‖ * (standardModule ℕ J).norm x :=
  Adjointable.norm_apply_le_opNorm T.isBounded x

/-- The norm is nonnegative (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.norm_nonneg' (T : StdBdd J) : 0 ≤ ‖T‖ := Adjointable.opNorm_nonneg _

/-- Scalar multiplication is norm-bounded (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.norm_smul_le (c : ℂ) (T : StdBdd J) : ‖c • T‖ ≤ ‖c‖ * ‖T‖ := by
  show (Adjointable.smul c T.1).opNorm ≤ ‖c‖ * T.1.opNorm
  exact Adjointable.opNorm_le_of_bound
    (mul_nonneg (norm_nonneg c) (Adjointable.opNorm_nonneg _))
    ((Adjointable.isBoundedBy_opNorm T.isBounded).smul c)

/-- The norm is homogeneous (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.norm_smul_eq (c : ℂ) (T : StdBdd J) : ‖c • T‖ = ‖c‖ * ‖T‖ := by
  refine le_antisymm (StdBdd.norm_smul_le c T) ?_
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, norm_zero, zero_mul]
    exact StdBdd.norm_nonneg' _
  · have h := StdBdd.norm_smul_le c⁻¹ (c • T)
    rw [inv_smul_smul₀ hc] at h
    calc ‖c‖ * ‖T‖ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • T‖) := mul_le_mul_of_nonneg_left h (norm_nonneg c)
      _ = ‖c • T‖ := by
        rw [← mul_assoc, ← norm_mul c c⁻¹, mul_inv_cancel₀ hc, norm_one, one_mul]

/-- The triangle inequality (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.norm_add_le' (T U : StdBdd J) : ‖T + U‖ ≤ ‖T‖ + ‖U‖ := by
  show (T.1.add U.1).opNorm ≤ T.1.opNorm + U.1.opNorm
  exact Adjointable.opNorm_add_le T.isBounded U.isBounded

/-- The norm is definite (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.norm_eq_zero_iff' (T : StdBdd J) : ‖T‖ = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply adjointable_ext
    intro x
    have h1 := StdBdd.norm_apply_le T x
    rw [h, zero_mul] at h1
    have h2 : (standardModule ℕ J).norm (T.1.toFun x) = 0 :=
      le_antisymm h1 ((standardModule ℕ J).norm_nonneg _)
    exact (((standardModule ℕ J).norm_eq_zero_iff _).mp h2).trans (zero_toFun x).symm
  · intro h
    rw [h]
    show (Adjointable.zero (standardModule ℕ J) (standardModule ℕ J)).opNorm = 0
    exact Adjointable.opNorm_zero

/-- The normed-space core of `𝓛(H_J)` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.normedSpaceCore : NormedSpace.Core ℂ (StdBdd J) where
  norm_nonneg := StdBdd.norm_nonneg'
  norm_smul := StdBdd.norm_smul_eq
  norm_triangle := StdBdd.norm_add_le'
  norm_eq_zero_iff := StdBdd.norm_eq_zero_iff'

/-- `𝓛(H_J)` is a normed group under the operator norm (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
instance StdBdd.instNormedAddCommGroup : NormedAddCommGroup (StdBdd J) :=
  NormedAddCommGroup.ofCore StdBdd.normedSpaceCore

/-- Submultiplicativity (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem StdBdd.norm_mul_le' (T U : StdBdd J) : ‖T * U‖ ≤ ‖T‖ * ‖U‖ := by
  show (T.1.comp U.1).opNorm ≤ T.1.opNorm * U.1.opNorm
  exact Adjointable.opNorm_comp_le T.isBounded U.isBounded

/-- `𝓛(H_J)` is a normed ring (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`;
Lance Ch. 1). -/
instance StdBdd.instNormedRing : NormedRing (StdBdd J) where
  __ := StdBdd.instNormedAddCommGroup
  __ := (inferInstance : Ring (StdBdd J))
  norm_mul_le := StdBdd.norm_mul_le'

/-- `𝓛(H_J)` is a normed `ℂ`-algebra (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
instance StdBdd.instNormedAlgebra : NormedAlgebra ℂ (StdBdd J) :=
  { (inferInstance : Algebra ℂ (StdBdd J)) with norm_smul_le := StdBdd.norm_smul_le }

/-- **The C⋆-identity on `𝓛(H_J)`** (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`;
Lance, Prop. 1.2 and §2). -/
instance StdBdd.instCStarRing : CStarRing (StdBdd J) where
  norm_mul_self_le T := by
    show T.1.opNorm * T.1.opNorm ≤ ((Adjointable.adjoint T.1).comp T.1).opNorm
    rw [Adjointable.opNorm_adjoint_comp_self T.isBounded, pow_two]

end

end GroupApproximation.Full.TWWSchafhauser
