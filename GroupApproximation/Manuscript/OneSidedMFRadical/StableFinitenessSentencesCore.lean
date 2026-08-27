import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceStableFiniteProofClosure
import GroupApproximation.Sofic.KazhdanCornerPolar
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Shared engine for the `lem:stable-finite` proof-sentence census

`non_mf_groups_exist.tex`, Lemma `lem:stable-finite` (lines 560-597), is
formalized as a closed proposition in
`Manuscript/OneSidedMFRadical/StableFiniteness.lean`
(`manuscriptNormMatrixCoronaStableFinite`), but by a route that does *not*
literally follow the printed proof: it reaches finiteness through the
Neumann-series correction of `Analysis/MatrixCoronaDedekindFinite.lean` and
the abstract Murray-von-Neumann comparison of
`Analysis/FiniteCStarMurrayVonNeumann.lean`.  The printed proof of
`lem:stable-finite` (lines 581-596) is a *different, concrete* argument: lift
`v` to a bounded sequence `(x_n)`, correct each coordinate by the finite-matrix
polar decomposition `u_n = x_n(x_n^*x_n)^{-1/2}` wherever it is defined, patch
the finitely many bad coordinates to `1`, and read off `vv^*=1` from
pointwise unitarity of the patched lift.  That concrete route is exactly what
`Sofic/KazhdanCornerPolar.lean` (`KazhdanCornerMatrices.polarCorrect`,
`.polarCorrectUnitary`, `.norm_polarCorrect_sub_le_mul`) and
`Analysis/PrintedLiftingSteps.lean`/`Analysis/NormMatrixCoronaUnitary.lean`
already build, for the closely related "unitary lifting" lemma at the same
norm-matrix corona.  This file assembles the same concrete route as a
reusable engine, generic in the base family of finite index types, so that:

* `Manuscript/OneSidedMFRadical/StableFinitenessSentences.lean` can state one
  Lean declaration per printed proof *sentence* of `lem:stable-finite`,
  following the printed dependency order, and
* the printed sentence "for every `k ≥ 1`, apply this construction with
  matrix sizes `km_n`" (proof-ledger key `993df6a79c44`) can literally
  *re-apply* the same engine at the amplified index family, rather than
  restate it.

## What is proved, and what is not

Every declaration below is proved unconditionally from repository inputs
that already exist on `origin/main`
(`Sofic/KazhdanCornerPolar.lean`, `Analysis/NormMatrixCorona.lean`,
`Manuscript/OneSidedMFRadical/SentenceStableFiniteProofClosure.lean`).  The
one genuinely new piece of mathematics assembled here is
`isUnit_cornerGram_of_eigenvalues_pos`: invertibility of `x_n^*x_n` from
positivity of its eigenvalues, computed through the determinant (a strictly
positive product of eigenvalues) rather than assumed.  This mirrors the
determinant computation already carried out for a different Hermitian
display in `Sofic/ExteriorMFProfile.det_one_sub_smul_eq_prod_eigenvalues`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace StableFinitenessSentencesCore

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Invertibility of the Gram matrix, from positivity of its eigenvalues

The printed proof's step "the matrix `x_n^*x_n` is invertible" is computed
here through the determinant: a Hermitian matrix with strictly positive
eigenvalues has determinant a nonzero product of those eigenvalues, hence is
a unit. -/

private theorem det_cornerGram_eq_prod_eigenvalues {Z : Type*} [Fintype Z]
    [DecidableEq Z] (C : Matrix Z Z ℂ)
    (hP : (KazhdanCornerMatrices.cornerGram C).IsHermitian) :
    (KazhdanCornerMatrices.cornerGram C).det =
      ∏ i : Z, (hP.eigenvalues i : ℂ) := by
  conv_lhs => rw [hP.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hdetu : (hP.eigenvectorUnitary : Matrix Z Z ℂ).det *
      (star hP.eigenvectorUnitary : Matrix Z Z ℂ).det = 1 := by
    rw [← Matrix.det_mul,
      Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2, Matrix.det_one]
  calc
    (hP.eigenvectorUnitary : Matrix Z Z ℂ).det *
          (Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)).det *
        (star hP.eigenvectorUnitary : Matrix Z Z ℂ).det
      = (Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)).det *
          ((hP.eigenvectorUnitary : Matrix Z Z ℂ).det *
            (star hP.eigenvectorUnitary : Matrix Z Z ℂ).det) := by ring
    _ = (Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)).det := by
          rw [hdetu, mul_one]
    _ = ∏ i : Z, (hP.eigenvalues i : ℂ) := by
          rw [Matrix.det_diagonal]
          exact Finset.prod_congr rfl fun i _ ↦ by simp [Function.comp_apply]

/-- **Invertibility from positive eigenvalues.**  The determinant route to
"the matrix `x_n^*x_n` is invertible" (`lem:stable-finite`, proof sentence
`fc7ae023c534`). -/
theorem isUnit_cornerGram_of_eigenvalues_pos {Z : Type*} [Fintype Z]
    [DecidableEq Z] (C : Matrix Z Z ℂ)
    (hP : (KazhdanCornerMatrices.cornerGram C).IsHermitian)
    (hpos : ∀ i, 0 < hP.eigenvalues i) :
    IsUnit (KazhdanCornerMatrices.cornerGram C) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_cornerGram_eq_prod_eigenvalues C hP]
  refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
  exact_mod_cast (hpos i).ne'

/-- The manuscript's two notations for the Gram matrix, `x_n^*x_n` and
`KazhdanCornerMatrices.cornerGram (x n)`, agree. -/
theorem cornerGram_eq_star_mul_self {Z : Type*} [Fintype Z] [DecidableEq Z]
    (C : Matrix Z Z ℂ) : KazhdanCornerMatrices.cornerGram C = star C * C := by
  rw [KazhdanCornerMatrices.cornerGram, Matrix.star_eq_conjTranspose]

variable {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]
  [∀ n, Nonempty (Y n)]

/-! ## The printed corrected sequence `u_n`, patched to `1` off the good set -/

/-- **The printed patched sequence.**  At a coordinate where the Gram defect
of the given bounded lift is at most `1/2`, this is the printed polar
correction `x_n(x_n^*x_n)^{-1/2}`; at the finitely many remaining
coordinates it is `1` ("assigning arbitrary unitary values to the finitely
many remaining coordinates", proof sentence `ee3d6cbf975d`). -/
def polarPatch (x : BoundedMatrixSequence Y) (n : ℕ) : Matrix (Y n) (Y n) ℂ :=
  if _h : ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ) then
    KazhdanCornerMatrices.polarCorrect (x n)
      (KazhdanCornerMatrices.cornerGram_isHermitian (x n))
  else 1

omit [∀ n, Nonempty (Y n)] in
theorem polarPatch_of_good (x : BoundedMatrixSequence Y) {n : ℕ}
    (hn : ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ)) :
    polarPatch x n = KazhdanCornerMatrices.polarCorrect (x n)
      (KazhdanCornerMatrices.cornerGram_isHermitian (x n)) :=
  dif_pos hn

omit [∀ n, Nonempty (Y n)] in
theorem polarPatch_of_not_good (x : BoundedMatrixSequence Y) {n : ℕ}
    (hn : ¬ ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ)) :
    polarPatch x n = 1 :=
  dif_neg hn

omit [∀ n, Nonempty (Y n)] in
/-- Each patched coordinate is unitary: the printed polar correction where
it applies, and the identity (trivially unitary) elsewhere. -/
theorem polarPatch_mem_unitary (x : BoundedMatrixSequence Y) (n : ℕ) :
    polarPatch x n ∈ Matrix.unitaryGroup (Y n) ℂ := by
  by_cases hn : ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ)
  · rw [polarPatch_of_good x hn]
    exact KazhdanCornerMatrices.polarCorrect_mem_unitaryGroup (x n)
      (KazhdanCornerMatrices.cornerGram_isHermitian (x n))
      (KazhdanCornerMatrices.cornerGram_eigenvalues_pos_of_norm_sub_one_le
        (x n) (KazhdanCornerMatrices.cornerGram_isHermitian (x n)) hn le_rfl)
  · rw [polarPatch_of_not_good x hn, Matrix.mem_unitaryGroup_iff']
    simp

/-- A unitary matrix has norm exactly `1`, so the patched coordinate is
bounded uniformly by `1`; the patch itself needs this to be a genuine
element of `BoundedMatrixSequence Y`. -/
theorem polarPatch_norm_le_one (x : BoundedMatrixSequence Y) (n : ℕ) :
    ‖polarPatch x n‖ ≤ 1 :=
  le_of_eq (CStarRing.norm_of_mem_unitary (polarPatch_mem_unitary x n))

/-- **The printed patched sequence, as a genuine bounded sequence.** -/
def polarPatchSeq (x : BoundedMatrixSequence Y) : BoundedMatrixSequence Y :=
  ⟨polarPatch x, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact polarPatch_norm_le_one x n⟩⟩

@[simp] theorem polarPatchSeq_apply (x : BoundedMatrixSequence Y) (n : ℕ) :
    polarPatchSeq x n = polarPatch x n := rfl

/-! ## The convergence and lifting clauses -/

omit [∀ n, Nonempty (Y n)] in
/-- **"`‖u_n-x_n‖→0`."**  The patched sequence converges to the given lift in
the coordinate operator norm, uniformly along the cofinite filter (proof
sentence `ee3d6cbf975d`, first clause). -/
theorem polarPatch_tendsto_sub (x : BoundedMatrixSequence Y)
    (hgram : Tendsto (fun n ↦ ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖)
      cofinite (nhds 0)) :
    Tendsto (fun n ↦ ‖polarPatch x n - x n‖) cofinite (nhds 0) := by
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgram) (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  refine squeeze_zero'
    (g := fun n ↦ ‖x‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖))
    (Eventually.of_forall fun n ↦ norm_nonneg (polarPatch x n - x n)) ?_ ?_
  · filter_upwards [hgood] with n hn
    show ‖polarPatch x n - x n‖ ≤
      ‖x‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖)
    rw [polarPatch_of_good x hn]
    calc ‖KazhdanCornerMatrices.polarCorrect (x n)
            (KazhdanCornerMatrices.cornerGram_isHermitian (x n)) - x n‖
        ≤ ‖x n‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖) :=
          KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul (x n)
            (KazhdanCornerMatrices.cornerGram_isHermitian (x n))
            (norm_nonneg _) hn le_rfl
      _ ≤ ‖x‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖) :=
          mul_le_mul_of_nonneg_right (boundedMatrixSequence_coord_norm_le Y x n)
            (by positivity)
  · simpa using (hgram.const_mul 2).const_mul ‖x‖

/-- **"`(u_n)` is a unitary lift of `v`."**  If `x` is a bounded lift of `v`
and its Gram defect is null, the patched sequence is again a lift of `v`
(proof sentence `ee3d6cbf975d`, second clause). -/
theorem polarPatchSeq_mk_eq {v : NormMatrixCStarCorona Y}
    {x : BoundedMatrixSequence Y}
    (hx : normMatrixCStarCoronaMk Y x = v)
    (hgram : Tendsto (fun n ↦ ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖)
      cofinite (nhds 0)) :
    normMatrixCStarCoronaMk Y (polarPatchSeq x) = v := by
  have hnull : IsNullMatrixSequence Y cofinite (polarPatchSeq x - x) :=
    polarPatch_tendsto_sub x hgram
  rw [← hx, ← sub_eq_zero, ← map_sub]
  exact (normMatrixCStarCoronaMk_eq_zero_iff Y _).mpr hnull

/-! ## The conclusion: an isometry of the corona is a unitary -/

/-- **The printed proof of `lem:stable-finite`, assembled.**  Every isometry
of a norm-matrix corona is a unitary (proof sentences `8461ba613634`
through `b21cf7f0f627`, chained).  Stated generically in the base family so
that the printed sentence `993df6a79c44` ("apply this construction with
matrix sizes `km_n`") can literally re-invoke it at the amplified family. -/
theorem isometry_eq_unitary {v : NormMatrixCStarCorona Y}
    (hv : star v * v = 1) : v * star v = 1 := by
  obtain ⟨x, hx⟩ := normMatrixCStarCoronaMk_surjective Y v
  have hgramRaw : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) :=
    manuscriptStableFiniteBoundedLiftGramDefect Y v x hx hv
  have hgram : Tendsto (fun n ↦ ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖)
      cofinite (nhds 0) := by
    simpa only [cornerGram_eq_star_mul_self] using hgramRaw
  have hmk : normMatrixCStarCoronaMk Y (polarPatchSeq x) = v :=
    polarPatchSeq_mk_eq hx hgram
  have hpt : ∀ n, polarPatch x n * star (polarPatch x n) = 1 := fun n ↦
    Unitary.mul_star_self_of_mem (polarPatch_mem_unitary x n)
  have huv : polarPatchSeq x * star (polarPatchSeq x) = 1 := by
    ext n i j
    exact congrArg (fun A : Matrix (Y n) (Y n) ℂ ↦ A i j) (hpt n)
  rw [← hmk]
  have hstar := normMatrixCStarCorona_star_mk Y (polarPatchSeq x)
  rw [hstar, ← map_mul, huv, map_one]

end

end StableFinitenessSentencesCore
end OneSidedMFRadical
end Manuscript
end GroupApproximation
