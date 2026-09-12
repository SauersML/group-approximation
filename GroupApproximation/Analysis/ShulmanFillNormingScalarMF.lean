import GroupApproximation.Analysis.MFAlgebraDimensionNormalization

/-!
# The scalars are MF-embeddable

`HasMFEmbedding ℂ` is standard and true — `ℂ` is one-dimensional, so it embeds
in a matricial corona by constants — but this repository does not package it.
Its three introduction lemmas are
`MFAlgebraMatrixAmplification.hasMFEmbedding_cstarMatrix`, which amplifies an
algebra that already has the property, `hasMFEmbedding_iff`, which normalises
the dimension sequence, and `ShulmanFill.hasMFEmbedding_boundedMatrixSequence`,
which is about a bounded product.  None of them starts anywhere.  This module
supplies the base case, so that
`Analysis/ShulmanFillNormingTheorem4Refuted.not_theorem4ModelFirst` carries no
hypothesis at all.

The witness is the constant sequence of one-by-one scalar matrices.  Its class
in the cofinite corona is zero exactly when its coordinate norms tend to zero
along `cofinite`; the norms are constant at `‖z • 1‖`, and `cofinite` on `ℕ` is
`NeBot`, so the class vanishes only for `z = 0`.  Nothing about the corona's
norm has to be computed.

The `CStarAlgebra` structure on a matrix block is a `local instance` at one
index type, following `Analysis/PolarLiftingMatrixBlocks`: `Matrix` carries
several norms in mathlib and they are scoped deliberately, so the choice is made
inside this file only, and stated at a single block rather than against a family
variable — as a parametric instance over `ℕ` with no forward dependencies Lean
declines to use it.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

open scoped Matrix.Norms.L2Operator

noncomputable section

section ScalarMF

/-- The bundled C-star structure on one matrix block at the L2 operator norm. -/
local instance matrixBlockCStarAlgebraForScalarMF (Z : Type) [Fintype Z]
    [DecidableEq Z] [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The one-by-one models.  `HasUnrestrictedMFEmbedding` quantifies over
`ℕ → FiniteModel`, not over a bare type family, so the bundle is what has to be
supplied. -/
abbrev scalarModel : ℕ → FiniteModel := fun _ ↦ ⟨Fin 1, inferInstance, inferInstance⟩

instance nonempty_scalarModel (n : ℕ) : Nonempty (scalarModel n) :=
  inferInstanceAs (Nonempty (Fin 1))

/-- The constant sequence of scalar one-by-one matrices. -/
def scalarMatrixSeq (z : ℂ) : BoundedMatrixSequence (fun n ↦ scalarModel n) :=
  ⟨fun _ ↦ z • (1 : Matrix (Fin 1) (Fin 1) ℂ),
    memℓp_infty ⟨‖z • (1 : Matrix (Fin 1) (Fin 1) ℂ)‖, by
      rintro _ ⟨n, rfl⟩
      exact le_rfl⟩⟩

@[simp] theorem scalarMatrixSeq_apply (z : ℂ) (n : ℕ) :
    scalarMatrixSeq z n = z • (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl

/-- The constant scalar sequence, as a `*`-homomorphism. -/
def scalarMatrixHom : ℂ →⋆ₙₐ[ℂ] BoundedMatrixSequence (fun n ↦ scalarModel n) where
  toFun := scalarMatrixSeq
  map_zero' := by
    refine lp.ext (funext fun n ↦ ?_)
    show (0 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)
      = (0 : BoundedMatrixSequence (fun n ↦ scalarModel n)) n
    rw [zero_smul]
    rfl
  map_add' x y := by
    refine lp.ext (funext fun n ↦ ?_)
    show (x + y) • (1 : Matrix (Fin 1) (Fin 1) ℂ)
      = (scalarMatrixSeq x + scalarMatrixSeq y) n
    rw [lp.coeFn_add, Pi.add_apply, scalarMatrixSeq_apply, scalarMatrixSeq_apply,
      add_smul]
  map_mul' x y := by
    refine lp.ext (funext fun n ↦ ?_)
    show (x * y) • (1 : Matrix (Fin 1) (Fin 1) ℂ)
      = (scalarMatrixSeq x * scalarMatrixSeq y) n
    rw [lp.infty_coeFn_mul, Pi.mul_apply, scalarMatrixSeq_apply,
      scalarMatrixSeq_apply, smul_mul_assoc, one_mul, smul_smul]
  map_smul' r x := by
    refine lp.ext (funext fun n ↦ ?_)
    show (r * x) • (1 : Matrix (Fin 1) (Fin 1) ℂ) = (r • scalarMatrixSeq x) n
    rw [lp.coeFn_smul, Pi.smul_apply, scalarMatrixSeq_apply, mul_smul]
  map_star' x := by
    refine lp.ext (funext fun n ↦ ?_)
    show (star x) • (1 : Matrix (Fin 1) (Fin 1) ℂ) = (star (scalarMatrixSeq x)) n
    rw [lp.coeFn_star, Pi.star_apply, scalarMatrixSeq_apply, star_smul, star_one]

/-- The constant scalar sequence is null only if it is zero: its coordinate
norms are constant, and `cofinite` on `ℕ` is `NeBot`. -/
theorem eq_zero_of_isNull_scalarMatrixSeq {z : ℂ}
    (h : IsNullMatrixSequence (fun n ↦ scalarModel n) cofinite (scalarMatrixSeq z)) :
    z = 0 := by
  -- Every coordinate is the same scalar matrix, so the norm sequence is
  -- constant definitionally; `IsNullMatrixSequence` is a `def`, so its
  -- unfolding does not appear in `h`'s type and there is nothing to rewrite.
  have htend : Tendsto (fun _ : ℕ ↦ ‖z • (1 : Matrix (Fin 1) (Fin 1) ℂ)‖)
      cofinite (𝓝 0) := h
  have hzero : ‖z • (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ = 0 :=
    tendsto_const_nhds_iff.mp htend
  have hsmul : z • (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := norm_eq_zero.mp hzero
  rcases smul_eq_zero.mp hsmul with hz | h1
  · exact hz
  · exact absurd h1 one_ne_zero

/-- **The scalars are MF-embeddable.**  The constant one-by-one scalar sequence
is faithful in the cofinite corona. -/
theorem hasMFEmbedding_complex : HasMFEmbedding ℂ := by
  refine (MFAlgebraDimension.hasMFEmbedding_iff ℂ).2 ?_
  refine ⟨scalarModel, fun _ ↦ inferInstance, fun _ ↦ ?_, ?_⟩
  · simp
  · refine ⟨(normMatrixCStarCoronaQuotient (fun n ↦ scalarModel n)).toNonUnitalStarAlgHom.comp
      scalarMatrixHom, ?_⟩
    intro x y hxy
    have hsub : normMatrixCStarCoronaMk (fun n ↦ scalarModel n) (scalarMatrixSeq (x - y)) = 0 := by
      have hlin : scalarMatrixSeq (x - y) = scalarMatrixSeq x - scalarMatrixSeq y := by
        have := map_sub scalarMatrixHom x y
        exact this
      rw [hlin, map_sub]
      show normMatrixCStarCoronaMk (fun n ↦ scalarModel n) (scalarMatrixSeq x)
        - normMatrixCStarCoronaMk (fun n ↦ scalarModel n) (scalarMatrixSeq y) = 0
      rw [sub_eq_zero]
      exact hxy
    exact sub_eq_zero.mp
      (eq_zero_of_isNull_scalarMatrixSeq
        ((normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ scalarModel n) _).mp hsub))

end ScalarMF

end

end ShulmanFill
end GroupApproximation
