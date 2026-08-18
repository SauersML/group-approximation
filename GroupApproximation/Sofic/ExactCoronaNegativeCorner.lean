import GroupApproximation.Sofic.NegativeCornerModel
import GroupApproximation.Stability.MixedApproximation

/-!
# Exact in the corona, asymptotic in the matrices

The negative-corner cut produces two statements that are easy to conflate,
because in ordinary mathematical prose one writes both as "`Θ(w) = -1` on the
negative corner".

* At finite stage nothing is exact.  `NegativeCornerModel` returns an almost
  representation `B` with `‖B.map n z + 1‖ → 0`: the compressed corner
  microstates approach `-1` and, in general, never reach it.  Polar correction
  makes each corner unitary exactly, but not equal to `-1`.
* In the corona the same statement *is* exact.  The class of the sequence
  `(B.map n z)` in the cofinite norm-matrix corona is **equal**, on the nose,
  to the class of the constant sequence `-1`, because the two sequences differ
  by a null sequence.

The distinction is not pedantic.  Every use of the corner downstream --
centrality of the mark, the Kazhdan transport, the sign criterion -- is an
algebraic identity in the corona, and algebraic identities are available only
on the exact side.  Every *estimate* -- the leakage bounds, the multiplicative
defects, the corner rank statements -- lives at finite stage and is available
only on the asymptotic side.  A paragraph that cites the wrong one is citing a
theorem that does not support it.

This file states the pair, once, as a single theorem
(`negativeCorner_exact_in_corona_asymptotic_in_matrices`), so that a citation
can name the level it means.

Both halves are packaging: the finite-stage half is
`NegativeCornerModel.exists_negativeCorner_opAlmostRepresentation` verbatim,
and the corona half is the observation that eventual smallness of
`‖B.map n z + 1‖` is exactly membership of `(negOneSeq)⁻¹ · (B.map · z)` in
`nullCofiniteOpSubgroup`.  No new estimate is proved here.
-/

namespace GroupApproximation
namespace ExactCoronaNegativeCorner

open Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G]

/-! ## The constant sequence `-1` -/

theorem negOne_mem_unitaryGroup (Y : FiniteModel) :
    (-1 : Matrix Y Y ℂ) ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, one_mul]

/-- The central involution `-1` of the unitary group of one model. -/
noncomputable def negOneU (Y : FiniteModel) : Matrix.unitaryGroup Y ℂ :=
  ⟨-1, negOne_mem_unitaryGroup Y⟩

@[simp] theorem coe_negOneU (Y : FiniteModel) :
    ((negOneU Y : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) = -1 := rfl

/-- The constant sequence `-1`, a central involution of the unitary-sequence
group and hence of the corona. -/
noncomputable def negOneSeq (X : ℕ → FiniteModel) :
    ∀ n, Matrix.unitaryGroup (X n) ℂ :=
  fun n ↦ negOneU (X n)

/-- The class of the constant sequence `-1` in the cofinite corona. -/
noncomputable def coronaNegOne (X : ℕ → FiniteModel) :
    NormMatrixCoronaUnitary X :=
  QuotientGroup.mk (negOneSeq X)

/-! ## The exact corona identity -/

/-- Eventual convergence of a unitary sequence to `-1` in operator norm is
*exactly* equality with `-1` in the cofinite corona.  Nothing is lost and
nothing is approximated: the corona quotient is designed to turn this limit
into this identity. -/
theorem coronaMk_eq_coronaNegOne_of_tendsto {X : ℕ → FiniteModel}
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hv : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(v n : Matrix (X n) (X n) ℂ) + 1‖ ≤ ε) :
    (QuotientGroup.mk v : NormMatrixCoronaUnitary X) = coronaNegOne X := by
  rw [coronaNegOne, QuotientGroup.eq]
  intro ε hε
  obtain ⟨N, hN⟩ := hv (ε / 2) (by linarith)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  change opLength (X n) ((v n)⁻¹ * negOneU (X n)) < ε
  rw [opLength_inv_mul]
  have hrw : ((negOneU (X n) : Matrix.unitaryGroup (X n) ℂ) :
        Matrix (X n) (X n) ℂ) - (v n : Matrix (X n) (X n) ℂ)
      = -((v n : Matrix (X n) (X n) ℂ) + 1) := by
    rw [coe_negOneU]
    abel
  rw [hrw, norm_neg]
  exact (hN n hn).trans_lt (by linarith)

/-! ## The pair -/

/-- **Exact in the corona, asymptotic in the matrices.**

From a separated approximate central involution `z` there is an operator-norm
almost representation `B` for which:

* in the **corona**, `B.coronaHom z` is *equal* to the class of the constant
  sequence `-1` -- an identity, usable algebraically; and
* in the **matrices**, only `‖B.map n z + 1‖ → 0` -- an estimate, with no
  stage at which equality is claimed.

The two clauses are the same mathematical fact read at two levels, and the
theorem exists so that a citation names which level it uses. -/
theorem negativeCorner_exact_in_corona_asymptotic_in_matrices
    (A : OpAlmostRepresentation G) {z : G} (hz : z * z = 1)
    (hcentral : ∀ g : G, z * g = g * z)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∃ N, ∀ n ≥ N,
      delta ≤ ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖) :
    ∃ B : OpAlmostRepresentation G,
      B.coronaHom z = coronaNegOne B.model ∧
        ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          ‖(B.map n z : Matrix (B.model n) (B.model n) ℂ) + 1‖ ≤ ε := by
  obtain ⟨B, hB⟩ :=
    NegativeCornerModel.exists_negativeCorner_opAlmostRepresentation A hz
      hcentral hdelta hsep
  refine ⟨B, ?_, hB⟩
  have hmk : B.coronaHom z
      = (QuotientGroup.mk (fun n ↦ B.map n z) : NormMatrixCoronaUnitary B.model) :=
    rfl
  rw [hmk]
  exact coronaMk_eq_coronaNegOne_of_tendsto (fun n ↦ B.map n z) hB

end ExactCoronaNegativeCorner
end GroupApproximation
