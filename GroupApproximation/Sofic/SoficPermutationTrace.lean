import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.HyperlinearNonScalar
import GroupApproximation.Sofic.SoficEnvelopeExistence

/-!
# The permutation model of a sofic approximation, and its traces at `atTop`

A sofic approximation `σₙ : G → Sym(Xₙ)` gives finite unitary models
`Uₙ(g) = permMatrix (σₙ(g)⁻¹)`, and this file computes the limits of their
normalized traces.

**The inverse is not decoration.**  `Equiv.Perm.permMatrix` is an
*anti*-homomorphism (`AmenableQuasidiagonal.permMatrix_mul_permMatrix`), so
`g ↦ permMatrix (σₙ g)` reverses products.  Composing with inversion absorbs
the reversal, which is exactly what `isHyperlinear_of_isSofic` does and what
`modelUnitary` does here.

**The limits are ordinary limits.**  `normTrace_permMatrix` says the
normalized trace of a permutation matrix *is* `1 - d_Ham(σ, 1)`, with no phase
to hide behind, and the two asymptotic clauses of `SoficApproximation` are
ε-N statements at `atTop`.  So

`tr Uₙ(g) → 1` for `g = 1`  and  `tr Uₙ(g) → 0` for `g ≠ 1`

hold along `Filter.atTop`, with no ultrafilter anywhere.  That is what makes
the trace clause of a hyperlinear-trace model available without an
ultralimit-to-sequential equivalence theorem: soficity hands over the ordinary
limit directly.

The identity value is a limit here rather than an equality because a sofic
approximation only satisfies `σₙ(1) ≈ 1` — `SoficApproximation.map_one_close`
— and never `σₙ(1) = 1`.  Downstream, once these models are pushed into a
quotient where the map is a genuine group homomorphism, the identity value
becomes exact and this limit is not needed for it; it is needed for the trace
clause on the *generators*, which is what the ε/3 extension to the whole
algebra consumes.
-/

namespace GroupApproximation
namespace SoficPermutationTrace

open Filter Matrix
open scoped Matrix.Norms.L2Operator Topology

variable {G : Type*} [Group G]

/-- The finite unitary model of a sofic approximation: the permutation matrix
of the *inverse* permutation, which turns the anti-homomorphism `permMatrix`
into a homomorphism. -/
noncomputable def modelUnitary (S : SoficApproximation G) (n : ℕ) (g : G) :
    Matrix (S.model n) (S.model n) ℂ :=
  ((S.map n g)⁻¹).permMatrix ℂ

/-- The models are exactly unitary, not approximately so. -/
theorem modelUnitary_mem_unitaryGroup (S : SoficApproximation G) (n : ℕ)
    (g : G) :
    modelUnitary S n g ∈ Matrix.unitaryGroup (S.model n) ℂ :=
  permMatrix_mem_unitaryGroup _ _

/-- **The trace of the model is `1` minus the Hamming distance to the
identity**, with the inversion invisible: Hamming distance is inversion
invariant. -/
theorem normTrace_modelUnitary (S : SoficApproximation G)
    (hpos : ∀ n, 0 < Fintype.card (S.model n)) (n : ℕ) (g : G) :
    normTrace (S.model n) (modelUnitary S n g)
      = ((1 - hammingDistance (S.model n) (S.map n g) 1 : ℝ) : ℂ) := by
  have hinv : hammingDistance (S.model n) ((S.map n g)⁻¹) 1
      = hammingDistance (S.model n) (S.map n g) 1 := by
    have h0 := hammingDistance_inv (S.model n) (S.map n g) 1
    rwa [inv_one] at h0
  rw [modelUnitary, normTrace_permMatrix _ _ (hpos n), hinv]

/-! ## The two ordinary limits -/

/-- **At the identity the trace tends to `1`.**  Approximate multiplicativity
forces `σₙ(1)` towards the identity permutation. -/
theorem tendsto_normTrace_modelUnitary_one (S : SoficApproximation G)
    (hpos : ∀ n, 0 < Fintype.card (S.model n)) :
    Tendsto (fun n ↦ normTrace (S.model n) (modelUnitary S n 1)) atTop
      (nhds 1) := by
  have hreal : Tendsto
      (fun n ↦ (1 - hammingDistance (S.model n) (S.map n 1) 1 : ℝ)) atTop
      (nhds 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := S.map_one_close ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 := hN n hn
    have h2 := hammingDistance_nonnegative (S.model n) (S.map n 1) 1
    rw [Real.dist_eq]
    have hsimp : (1 - hammingDistance (S.model n) (S.map n 1) 1) - 1
        = -hammingDistance (S.model n) (S.map n 1) 1 := by ring
    rw [hsimp, abs_neg, abs_of_nonneg h2]
    exact h1
  have hcx := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hreal
  rw [Complex.ofReal_one] at hcx
  refine hcx.congr fun n ↦ ?_
  exact (normTrace_modelUnitary S hpos n 1).symm

/-- **Away from the identity the trace tends to `0`.**  Asymptotic
faithfulness pushes the Hamming distance to `1`, and the trace is `1` minus
it.  The limit is along `atTop`: no ultrafilter is used or needed. -/
theorem tendsto_normTrace_modelUnitary_of_ne_one (S : SoficApproximation G)
    (hpos : ∀ n, 0 < Fintype.card (S.model n)) {g : G} (hg : g ≠ 1) :
    Tendsto (fun n ↦ normTrace (S.model n) (modelUnitary S n g)) atTop
      (nhds 0) := by
  have hreal : Tendsto
      (fun n ↦ (1 - hammingDistance (S.model n) (S.map n g) 1 : ℝ)) atTop
      (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := S.asymptoticallyFaithful g hg ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 := hN n hn
    have h2 := hammingDistance_le_one (S.model n) (S.map n g) 1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
    linarith
  have hcx := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  rw [Complex.ofReal_zero] at hcx
  refine hcx.congr fun n ↦ ?_
  exact (normTrace_modelUnitary S hpos n g).symm

/-- **The generator trace values of a sofic group, at `atTop`.**  Packaged as
the single statement the trace clause of a hyperlinear-trace model consumes:
a sofic approximation with positive models whose normalized traces converge to
the canonical values, all limits ordinary. -/
theorem exists_soficApproximation_tendsto_normTrace [Countable G]
    (h : IsSofic G) :
    ∃ S : SoficApproximation G, (∀ n, 0 < Fintype.card (S.model n)) ∧
      Tendsto (fun n ↦ normTrace (S.model n) (modelUnitary S n 1)) atTop
        (nhds 1) ∧
      ∀ g : G, g ≠ 1 →
        Tendsto (fun n ↦ normTrace (S.model n) (modelUnitary S n g)) atTop
          (nhds 0) := by
  obtain ⟨S, hpos⟩ :=
    SoficEnvelopeExistence.exists_positive_soficApproximation h
  exact ⟨S, hpos, tendsto_normTrace_modelUnitary_one S hpos,
    fun g hg ↦ tendsto_normTrace_modelUnitary_of_ne_one S hpos hg⟩

end SoficPermutationTrace
end GroupApproximation
