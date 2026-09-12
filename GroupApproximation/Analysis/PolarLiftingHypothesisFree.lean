import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.UnitInterval

/-!
# The polar-correction lifting needs no real rank zero and no semiprojectivity

The manuscript's paragraph *Unitary lifting is not matrix-specific* (grep the
tex for `"No real-rank-zero or semiprojectivity"`; probe `p:q5-lift`, row
`LI.19b` of `metadata/NON_MF_PROOF_LEDGER.md`) reads:

> If `u` is unitary in `∏_nA_n/⊕_nA_n` for unital `C⋆`-algebras `A_n`, and
> `(x_n)` is any bounded lift, then `‖x_n^*x_n-1‖→0` and `‖x_nx_n^*-1‖→0`.
> Thus `x_n` is invertible for all large `n`, and the polar correction
> `u_n=x_n(x_n^*x_n)^{-1/2}` is unitary with `‖u_n-x_n‖→0`.  No real-rank-zero
> or semiprojectivity hypothesis is needed for this lifting step in the sense
> of Loring.

`Analysis/PolarLiftingGeneralCStar.printedUnitaryLifting_cofinite` is that
sentence over arbitrary unital blocks, which is already the generality
Question 5 asks about.  What this file adds is the *last clause*, which is the
one reason row `LI.19b` still holds its statement column: "with no
real-rank-zero or semiprojectivity hypothesis" is a claim about a proof, not a
proposition --- **unless** it is read as a claim about instances, which is how
it is read here.

## What a hypothesis-freeness claim can mean formally

A theorem does not use a hypothesis if it holds where the hypothesis fails.
So the clause is proved by exhibiting blocks that

* satisfy the theorem's actual hypotheses (unital `C⋆`-algebras), and
* provably fail real rank zero,

and by then instantiating the general theorem at them.  That is
`lifting_holds_at_blocks_without_realRankZero`: the conclusion of the printed
lifting sentence, at blocks with no real rank zero.

The blocks are `C(I, ℂ)`, continuous complex functions on the unit interval.
Real rank zero is taken in the Brown--Pedersen characterization that this
statement needs and that is elementary to state: the invertible self-adjoint
elements are dense in the self-adjoint elements.  `C(I, ℂ)` fails it for the
oldest reason there is --- the interval is connected.  The self-adjoint
element `t ↦ 2t-1` changes sign, any self-adjoint element within distance `1`
of it still changes sign, and a real-valued function that changes sign on a
connected space has a zero, hence is not invertible.  The proof below is that
argument and nothing else: `not_hasRealRankZero_block`.

## What is *not* claimed

**Semiprojectivity is not defined here and is not defined in the pinned
Mathlib.**  Formalizing it needs the category-theoretic lifting property for
`C⋆`-algebras, which the pin does not carry.  What stands in for it is the
shape of the theorem being instantiated: `printedUnitaryLifting` is universally
quantified over the block family and its proof is a *formula* --- the lift is
`polarLiftSeq A x`, an explicit function of the given lift, produced with no
appeal to any lifting property of a source algebra.  A semiprojectivity
hypothesis is what one would need if the lift were obtained by lifting
relations; here the lift is written down.  `polarLift_is_a_formula` records
exactly that and nothing more: one map, defined before any unitary is chosen,
corrects every lift of every unitary at once.

**No claim is made about Question 5 itself**, which is open: for which
separable `A_n` does every homomorphism `H → U(∏A_n/⊕A_n)` still kill `w`.
The manuscript's own answer to the *lifting* half of that question is what is
formalized here, namely that the lifting half is not where the matrix
structure enters.

One pin artifact is inherited from `PolarLiftingGeneralCStar` and is not a
weakening: the blocks carry `[∀ n, Nontrivial (A n)]`, because the pinned
Mathlib builds the unital ring structure on `lp A ∞` only under `NormOneClass`
of every block, which for a `C⋆`-algebra is exactly nontriviality.  It excludes
no unitary group, since the zero algebra has none, and `C(I, ℂ)` satisfies it.
-/

namespace GroupApproximation
namespace PolarLiftingHypothesisFree

open Filter PolarLiftingGeneralCStar unitInterval

noncomputable section

/-! ## Real rank zero -/

/-- **Real rank zero**, in the Brown--Pedersen characterization: the
invertible self-adjoint elements are dense in the self-adjoint elements.  This
is the form the hypothesis-freeness claim needs; no other form is used or
proved equivalent here. -/
def HasRealRankZero (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ a : A, IsSelfAdjoint a → ∀ ε : ℝ, 0 < ε →
    ∃ b : A, IsSelfAdjoint b ∧ IsUnit b ∧ ‖a - b‖ < ε

/-! ## The blocks: continuous functions on the interval -/

/-- The block algebra.  Unital, commutative, and connected in the only sense
that matters below. -/
abbrev block : Type := C(I, ℂ)

/-- The left endpoint of the interval. -/
def endpoint0 : I := ⟨0, unitInterval.zero_mem⟩

/-- The right endpoint of the interval. -/
def endpoint1 : I := ⟨1, unitInterval.one_mem⟩

/-- The sign-changing self-adjoint element `t ↦ 2t-1`. -/
def signChange : block :=
  ⟨fun t ↦ ((2 * (t : ℝ) - 1 : ℝ) : ℂ), by
    have h : Continuous fun t : I ↦ (2 * (t : ℝ) - 1 : ℝ) :=
      (continuous_const.mul continuous_subtype_val).sub continuous_const
    exact Complex.continuous_ofReal.comp h⟩

theorem signChange_isSelfAdjoint : IsSelfAdjoint signChange := by
  show star signChange = signChange
  refine ContinuousMap.ext fun t ↦ ?_
  rw [ContinuousMap.star_apply]
  show (starRingEnd ℂ) (((2 * (t : ℝ) - 1 : ℝ) : ℂ)) = ((2 * (t : ℝ) - 1 : ℝ) : ℂ)
  exact Complex.conj_ofReal _

theorem signChange_endpoint0 : signChange endpoint0 = -1 := by
  have h0 : ((endpoint0 : ℝ)) = 0 := rfl
  show ((2 * ((endpoint0 : ℝ)) - 1 : ℝ) : ℂ) = -1
  rw [h0]
  norm_num

theorem signChange_endpoint1 : signChange endpoint1 = 1 := by
  have h1 : ((endpoint1 : ℝ)) = 1 := rfl
  show ((2 * ((endpoint1 : ℝ)) - 1 : ℝ) : ℂ) = 1
  rw [h1]
  norm_num

/-! ## Two elementary facts about `C(I, ℂ)` -/

/-- A self-adjoint continuous function is real-valued. -/
theorem im_eq_zero_of_isSelfAdjoint {g : block} (hg : IsSelfAdjoint g)
    (t : I) : (g t).im = 0 := by
  have h : star (g t) = g t := by
    rw [← ContinuousMap.star_apply]
    exact congrArg (fun f : block ↦ f t) hg
  refine Complex.conj_eq_iff_im.mp ?_
  rw [starRingEnd_apply]
  exact h

/-- An invertible continuous function vanishes nowhere. -/
theorem ne_zero_of_isUnit {g : block} (hg : IsUnit g) (t : I) : g t ≠ 0 := by
  obtain ⟨u, hu⟩ := hg
  intro hzero
  have hprod : (g * ((u⁻¹ : blockˣ) : block)) = 1 := by
    rw [← hu]
    exact u.mul_inv
  have hmul : g t * ((u⁻¹ : blockˣ) : block) t = 1 := by
    calc g t * ((u⁻¹ : blockˣ) : block) t
        = (g * ((u⁻¹ : blockˣ) : block)) t :=
          (ContinuousMap.mul_apply _ _ t).symm
      _ = (1 : block) t := by rw [hprod]
      _ = 1 := ContinuousMap.one_apply t
  rw [hzero, zero_mul] at hmul
  exact zero_ne_one hmul

/-! ## The blocks do not have real rank zero -/

/-- **`C(I, ℂ)` does not have real rank zero.**  The interval is connected, so
a self-adjoint element within distance `1` of `t ↦ 2t-1` is a real-valued
function that is negative at `0` and positive at `1`; the intermediate value
theorem gives it a zero, and a continuous function with a zero is not
invertible. -/
theorem not_hasRealRankZero_block : ¬ HasRealRankZero block := by
  intro hrr
  obtain ⟨g, hg, hgunit, hclose⟩ :=
    hrr signChange signChange_isSelfAdjoint 1 one_pos
  have hpt : ∀ t : I, ‖signChange t - g t‖ < 1 := by
    intro t
    calc ‖signChange t - g t‖ = ‖(signChange - g) t‖ := by
          rw [ContinuousMap.sub_apply]
      _ ≤ ‖signChange - g‖ := ContinuousMap.norm_coe_le_norm _ t
      _ < 1 := hclose
  have hb0 : ‖signChange endpoint0 - g endpoint0‖ < 1 := hpt endpoint0
  rw [signChange_endpoint0] at hb0
  have habs0 : |((-1 : ℂ) - g endpoint0).re| ≤ ‖(-1 : ℂ) - g endpoint0‖ :=
    Complex.abs_re_le_norm _
  have hre0 : ((-1 : ℂ) - g endpoint0).re = -1 - (g endpoint0).re := by simp
  rw [hre0] at habs0
  have hlt0 := abs_lt.mp (lt_of_le_of_lt habs0 hb0)
  have hg0 : (g endpoint0).re < 0 := by linarith [hlt0.1]
  have hb1 : ‖signChange endpoint1 - g endpoint1‖ < 1 := hpt endpoint1
  rw [signChange_endpoint1] at hb1
  have habs1 : |((1 : ℂ) - g endpoint1).re| ≤ ‖(1 : ℂ) - g endpoint1‖ :=
    Complex.abs_re_le_norm _
  have hre1 : ((1 : ℂ) - g endpoint1).re = 1 - (g endpoint1).re := by simp
  rw [hre1] at habs1
  have hlt1 := abs_lt.mp (lt_of_le_of_lt habs1 hb1)
  have hg1 : 0 < (g endpoint1).re := by linarith [hlt1.2]
  have hcont : Continuous fun t : I ↦ (g t).re :=
    Complex.continuous_re.comp g.continuous
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t : I ↦ (g t).re) endpoint0)
      ((fun t : I ↦ (g t).re) endpoint1) := ⟨hg0.le, hg1.le⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ endpoint0 endpoint1 hcont hmem
  refine ne_zero_of_isUnit hgunit t (Complex.ext ?_ ?_)
  · simpa using ht
  · simpa using im_eq_zero_of_isSelfAdjoint hg t

/-! ## The printed lifting, at blocks without real rank zero -/

/-- **The printed sentence, instantiated at blocks with no real rank zero.**
Every assertion of the paragraph holds verbatim over `A_n = C(I, ℂ)`: the two
Gram defects vanish, the lift is eventually invertible, its polar correction is
unitary, converges to it, and lifts the same class. -/
theorem printedUnitaryLifting_withoutRealRankZero
    (x : BoundedCStarSequence (fun _ : ℕ ↦ block))
    (hq : Ideal.Quotient.mk
        (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite) x ∈
      unitary (CStarProductCorona (fun _ : ℕ ↦ block) cofinite)) :
    Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) ∧
      Tendsto (fun n ↦ ‖x n * star (x n) - 1‖) cofinite (nhds 0) ∧
      (∀ᶠ n in cofinite, IsUnit (x n)) ∧
      (∀ n, polarLiftSeq (fun _ : ℕ ↦ block) x n ∈ unitary block) ∧
      Tendsto (fun n ↦ ‖polarLiftSeq (fun _ : ℕ ↦ block) x n - x n‖)
        cofinite (nhds 0) ∧
      Ideal.Quotient.mk (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite)
          (polarLiftSeq (fun _ : ℕ ↦ block) x) =
        Ideal.Quotient.mk (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite)
          x :=
  printedUnitaryLifting_cofinite (fun _ : ℕ ↦ block) x hq

/-- **The clause, as a proposition.**  The blocks do not have real rank zero,
and every unitary of their corona lifts to a sequence of unitaries anyway. -/
theorem lifting_holds_at_blocks_without_realRankZero :
    ¬ HasRealRankZero block ∧
      ∀ q : CStarProductCorona (fun _ : ℕ ↦ block) cofinite,
        q ∈ unitary (CStarProductCorona (fun _ : ℕ ↦ block) cofinite) →
        ∃ u : BoundedCStarSequence (fun _ : ℕ ↦ block),
          (∀ n, u n ∈ unitary block) ∧
            Ideal.Quotient.mk
              (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite) u = q :=
  ⟨not_hasRealRankZero_block,
    fun q hq ↦ exists_unitary_lift_cofinite (fun _ : ℕ ↦ block) q hq⟩

/-- **The correction is a formula, not a lifting property.**  One map, written
down before any unitary is chosen, simultaneously corrects every bounded lift
of every unitary of the corona.  This is what replaces a semiprojectivity
hypothesis: nothing is lifted, the lift is computed.  Semiprojectivity itself
is not definable in the pinned Mathlib and is not claimed about anything
here. -/
theorem polarLift_is_a_formula :
    ∃ L : BoundedCStarSequence (fun _ : ℕ ↦ block) →
        BoundedCStarSequence (fun _ : ℕ ↦ block),
      ∀ x : BoundedCStarSequence (fun _ : ℕ ↦ block),
        (∀ n, L x n ∈ unitary block) ∧
        (Ideal.Quotient.mk
            (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite) x ∈
          unitary (CStarProductCorona (fun _ : ℕ ↦ block) cofinite) →
          Tendsto (fun n ↦ ‖L x n - x n‖) cofinite (nhds 0) ∧
            Ideal.Quotient.mk
                (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite) (L x) =
              Ideal.Quotient.mk
                (nullCStarSequenceIdeal (fun _ : ℕ ↦ block) cofinite) x) :=
  ⟨polarLiftSeq (fun _ : ℕ ↦ block), fun x ↦
    ⟨polarLiftSeq_mem_unitary (fun _ : ℕ ↦ block) x, fun hq ↦
      let h := printedUnitaryLifting_cofinite (fun _ : ℕ ↦ block) x hq
      ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩⟩

end

end PolarLiftingHypothesisFree
end GroupApproximation
