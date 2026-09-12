import GroupApproximation.Analysis.VoiculescuQuasicentral
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# (V1c) The quasicentral approximate unit, positive, increasing, and normalised

Arveson's cut of a separable space into blocks forms `dⱼ = (e_{j+1} - e_j)^{1/2}`
from the quasicentral approximate unit, so it needs that unit to be **positive**
and **increasing** — neither of which the landed (V1) datum records.  This module
states the strengthened datum, checks it delivers exactly what the cut consumes,
and checks the clause set is consistent.  Building it is the next step and is not
here.

## Which half is free and which is not

Positivity is free from the existing construction: (V1a)'s members are the
orthogonal projections onto the nested spans `densePrefixSpan`, which are
positive and increasing, and `Analysis/VoiculescuProjectionAssembly` builds them
that way.  What is *not* free is monotonicity of the quasicentral unit, because
(V1b) replaces those projections by convex averages of late members
(`exists_stage_of_sequentialCompactUnit`).  Averaging preserves positivity and
destroys monotonicity: an average over indices `≥ N` need not dominate an average
over earlier ones.  So the real content of this module, when it is built, is the
further selection that restores the order — classically
`e' = e + (1-e)^{1/2} f (1-e)^{1/2}`, which is `≥ e` because the added term is
positive and `≤ 1` because that term is at most `1 - e`.

## Two clauses that the consumer forced, and this module records

Both were absent from the first draft of this datum, and both are of one kind:
the datum was weaker than the thing built on it.

**Summability, not nullity.**  `QuasicentralPartition.summable_comm` asks for
`Σⱼ ‖dⱼ S_k - S_k dⱼ‖ < ∞`, because the superposition estimate in
`Analysis/VoiculescuSuperposition` *sums* commutator norms.  Asking only that
those norms tend to zero — which is all the qualitative corona argument of
`Analysis/VoiculescuSqrtCommutator` gives — is strictly weaker and does not
feed that estimate.  Nor is it enough to ask for summability of the commutators
of the *differences* and pass to square roots afterwards: the estimate available
for the square root loses a power, and a summable sequence of reals need not have
a summable sequence of square roots, so that route yields nothing.  (That says
the implication is unavailable, not that it is false; no counterexample is
claimed here.)  So the clause has to be stated about the `dⱼ` themselves, and the
construction has to *select diagonally*: at stage `j`, choose the next member of
the unit so that the square-root commutator against `S₀, …, S_j` is below
`2⁻ʲ`.  The corona lemma is what makes that choice available at each stage — it
is necessary input, and it is not sufficient.

**The unit starts at zero.**  `QuasicentralPartition.tendsto_sum_sq` asks that
`Σⱼ dⱼ² = 1` strongly.  The sum telescopes to `e_N - e_0`, so without `e_0 = 0`
it converges to `1 - e_0`, not to `1`.  This is a normalisation and not a
restriction — the recursion that builds the unit begins at `0` — but it is a
clause the consumer needs and so it belongs in the datum.  `sum_pieceSqrt_sq` is
where it is spent, and `sum_piece_eq` is the same telescoping without it, so that
what the clause buys is visible.

## The model tests

`MonotoneCompactUnit.succ_sub` is the two-element-chain test, and it is stated in
the form the consumer needs rather than as a restatement of the hypothesis: the
successive difference is a positive compact contraction, which is exactly what
`(e_{j+1} - e_j)^{1/2}` requires of it.  A datum that recorded monotonicity but
not positivity, or positivity but not the upper bound, fails it.

`sum_pieceSqrt_sq` is the consumer-form test for the normalisation: the partial
sums of `dⱼ²` are exactly `e_N`, which is the numerator of the partition's
resolution of the identity.  A datum without `zero` gives `e_N - e_0` here and
fails.

`exists_monotoneCompactUnit_of_finiteDimensional` is the consistency test: on a
finite-dimensional space the unit that is `0` at index `0` and `1` afterwards
satisfies every clause at once, so the conjunction is satisfiable and no clause
contradicts another.  That is the check a strengthened datum most needs, since
strengthening is where clause sets go inconsistent — and note that the constant
unit `1`, which served before, now fails `zero`, so the test is not vacuous on
the new clause.  It is not vacuous on the summability clause either: the pieces
of this model are `1` and `0`, whose square roots are `1` and `0`.

`quasicentralApproximateUnitSeparable_of_monotone` records that this is a genuine
strengthening of the landed (V1): it implies it, so nothing was weakened while
adding the order.

## What is still owed

That `dⱼ` is compact.  The compacts are a closed two-sided `⋆`-ideal and the
non-unital continuous calculus does not leave one, but that is a separate
instance ladder and is not asserted here.  And that `e_N → 1` strongly, which is
the other half of `tendsto_sum_sq`; it follows from the absorption clause by
testing against rank-one operators, and is likewise not proved here.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The strengthened datum -/

/-- **(V1c) A sequential approximate unit for the compacts that is positive,
increasing, and starts at zero.**  The landed `SequentialCompactUnit` with the
order clauses Arveson's cut needs. -/
structure MonotoneCompactUnit (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] extends SequentialCompactUnit H where
  /-- Each member is positive. -/
  nonneg : ∀ n, 0 ≤ toFun n
  /-- Each member is dominated by the identity. -/
  le_one : ∀ n, toFun n ≤ 1
  /-- The members increase. -/
  mono : Monotone toFun
  /-- The unit starts at zero, so that the successive differences telescope to
  the members themselves rather than to `e_N - e_0`. -/
  zero : toFun 0 = 0

namespace MonotoneCompactUnit

variable (u : MonotoneCompactUnit H)

/-- The successive difference `e_{j+1} - e_j`. -/
def piece (j : ℕ) : H →L[ℂ] H := u.toFun (j + 1) - u.toFun j

/-- The partition piece `dⱼ = (e_{j+1} - e_j)^{1/2}`. -/
def pieceSqrt (j : ℕ) : H →L[ℂ] H := CFC.sqrt (u.piece j)

/-- **The two-element chain, in the form the cut consumes.**  The successive
difference of a monotone unit is a positive compact contraction — precisely what
`(e_{j+1} - e_j)^{1/2}` asks of it.  A datum recording monotonicity without
positivity, or positivity without the upper bound, fails one of the three. -/
theorem succ_sub (n : ℕ) :
    0 ≤ u.toFun (n + 1) - u.toFun n ∧
      u.toFun (n + 1) - u.toFun n ≤ 1 ∧
      IsCompactOperator (u.toFun (n + 1) - u.toFun n) := by
  refine ⟨sub_nonneg.mpr (u.mono (Nat.le_succ n)), ?_, ?_⟩
  · exact le_trans (sub_le_self _ (u.nonneg n)) (u.le_one (n + 1))
  · show IsCompactOperator ((⇑(u.toFun (n + 1)) : H → H) - ⇑(u.toFun n))
    exact (u.isCompact (n + 1)).sub (u.isCompact n)

theorem piece_nonneg (j : ℕ) : 0 ≤ u.piece j := (u.succ_sub j).1

theorem piece_le_one (j : ℕ) : u.piece j ≤ 1 := (u.succ_sub j).2.1

theorem piece_isCompact (j : ℕ) : IsCompactOperator (u.piece j) := (u.succ_sub j).2.2

theorem pieceSqrt_nonneg (j : ℕ) : 0 ≤ u.pieceSqrt j := CFC.sqrt_nonneg _

/-- The pieces are the squares of the partition pieces: this is what makes
`Σⱼ dⱼ²` a telescoping sum at all. -/
theorem pieceSqrt_mul_self (j : ℕ) : u.pieceSqrt j * u.pieceSqrt j = u.piece j :=
  CFC.sqrt_mul_sqrt_self _ (u.piece_nonneg j)

/-- The telescoping identity, without the normalisation.  Stated so that what
`zero` buys in `sum_pieceSqrt_sq` is visible. -/
theorem sum_piece_eq (N : ℕ) :
    ∑ j ∈ Finset.range N, u.piece j = u.toFun N - u.toFun 0 :=
  Finset.sum_range_sub u.toFun N

/-- **The consumer-form identity, and where `zero` is spent.**  The partial sums
of `dⱼ²` are the members of the unit themselves.  This is the numerator of
`QuasicentralPartition.tendsto_sum_sq`: once `e_N → 1` strongly, the squares
resolve the identity.  Without `zero` the right-hand side is `e_N - e_0` and the
resolution is off by `e_0`. -/
theorem sum_pieceSqrt_sq (N : ℕ) :
    ∑ j ∈ Finset.range N, u.pieceSqrt j * u.pieceSqrt j = u.toFun N := by
  simp only [u.pieceSqrt_mul_self]
  rw [u.sum_piece_eq N, u.zero, sub_zero]

end MonotoneCompactUnit

/-! ## The statement -/

/-- **(V1c) as a statement.**  Every separable Hilbert space has a positive
increasing sequential approximate unit for its compacts, starting at zero, that
is asymptotically central for a given countable family and whose successive
square-root differences have *summable* commutators against that family.

The second clause is the diagonal selection.  It is what
`QuasicentralPartition.summable_comm` consumes, and it is strictly stronger than
the qualitative statement that those commutator norms tend to zero. -/
def MonotoneQuasicentralStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (S : ℕ → (H →L[ℂ] H)),
      ∃ u : MonotoneCompactUnit H,
        (∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0)) ∧
          (∀ k, Summable fun j ↦ ‖u.pieceSqrt j * S k - S k * u.pieceSqrt j‖)

/-! ## The model tests -/

/-- **The clause set is consistent.**  On a finite-dimensional space the unit
that is `0` at index `0` and the identity afterwards satisfies every clause
simultaneously: it is compact because the identity of a finite-dimensional space
is, it is positive and bounded by its own bound, it increases, it starts at zero,
it commutes with everything from index one on, and it absorbs every operator
exactly from there.  Its pieces are `1` and then `0`, whose square roots are `1`
and `0`, so the summable clause holds with every term zero.  The constant unit
`1` used before now fails `zero`, so this test is not vacuous on the new
clauses. -/
theorem exists_monotoneCompactUnit_of_finiteDimensional (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (S : ℕ → (H →L[ℂ] H)) :
    ∃ u : MonotoneCompactUnit H,
      (∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0)) ∧
        (∀ k, Summable fun j ↦ ‖u.pieceSqrt j * S k - S k * u.pieceSqrt j‖) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℂ H
  have hone : IsCompactOperator ((1 : H →L[ℂ] H) : H → H) :=
    isCompactOperator_id_iff_locallyCompactSpace.mpr inferInstance
  have hnorm : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial H with h | h
    · haveI := h
      have hz : (1 : H →L[ℂ] H) = 0 := by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        rw [Subsingleton.elim x 0]
        simp
      rw [hz, norm_zero]
      norm_num
    · haveI := h
      exact le_of_eq norm_one
  have h0 : (if (0 : ℕ) = 0 then (0 : H →L[ℂ] H) else 1) = 0 := if_pos rfl
  have hs : ∀ m : ℕ, (if m + 1 = 0 then (0 : H →L[ℂ] H) else 1) = 1 := fun m ↦
    if_neg (Nat.succ_ne_zero m)
  let u : MonotoneCompactUnit H :=
    { toFun := fun n ↦ if n = 0 then 0 else 1
      isCompact := fun n ↦ by
        rcases n with _ | m
        · rw [h0]; exact isCompactOperator_zero
        · rw [hs m]; exact hone
      isSelfAdjoint := fun n ↦ by
        rcases n with _ | m
        · rw [h0]; exact IsSelfAdjoint.zero _
        · rw [hs m]; exact IsSelfAdjoint.one _
      norm_le := fun n ↦ by
        rcases n with _ | m
        · rw [h0, norm_zero]; norm_num
        · rw [hs m]; exact hnorm
      tendsto_left := fun T _ ↦
        tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn ↦ by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [hs m, one_mul, sub_self, norm_zero]
      nonneg := fun n ↦ by
        rcases n with _ | m
        · rw [h0]
        · rw [hs m]; exact zero_le_one
      le_one := fun n ↦ by
        rcases n with _ | m
        · rw [h0]; exact zero_le_one
        · rw [hs m]
      mono := monotone_nat_of_le_succ fun n ↦ by
        rcases n with _ | m
        · rw [h0, hs 0]; exact zero_le_one
        · rw [hs m, hs (m + 1)]
      zero := h0 }
  have hpiece : ∀ j, u.piece j = if j = 0 then (1 : H →L[ℂ] H) else 0 := by
    intro j
    rcases j with _ | m
    · show (if (0 : ℕ) + 1 = 0 then (0 : H →L[ℂ] H) else 1)
        - (if (0 : ℕ) = 0 then (0 : H →L[ℂ] H) else 1) = _
      rw [h0, hs 0, sub_zero, if_pos rfl]
    · show (if m + 1 + 1 = 0 then (0 : H →L[ℂ] H) else 1)
        - (if m + 1 = 0 then (0 : H →L[ℂ] H) else 1) = _
      rw [hs m, hs (m + 1), sub_self, if_neg (Nat.succ_ne_zero m)]
  have hsqrt : ∀ j, u.pieceSqrt j = if j = 0 then (1 : H →L[ℂ] H) else 0 := by
    intro j
    show CFC.sqrt (u.piece j) = _
    rw [hpiece j]
    by_cases h : j = 0
    · rw [if_pos h]
      exact CFC.sqrt_unique (one_mul 1) zero_le_one
    · rw [if_neg h]
      exact CFC.sqrt_zero
  refine ⟨u, fun k ↦ ?_, fun k ↦ ?_⟩
  · refine tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn ↦ ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show ‖(if m + 1 = 0 then (0 : H →L[ℂ] H) else 1) * S k
      - S k * (if m + 1 = 0 then (0 : H →L[ℂ] H) else 1)‖ = 0
    rw [hs m, one_mul, mul_one, sub_self, norm_zero]
  · have hzero : (fun j ↦ ‖u.pieceSqrt j * S k - S k * u.pieceSqrt j‖)
      = fun _ : ℕ ↦ (0 : ℝ) := by
      funext j
      rw [hsqrt j]
      by_cases h : j = 0
      · rw [if_pos h, one_mul, mul_one, sub_self, norm_zero]
      · rw [if_neg h, zero_mul, mul_zero, sub_self, norm_zero]
    rw [hzero]
    exact summable_zero

/-- **The strengthening is a strengthening.**  The monotone statement implies the
landed (V1), so adding the order clauses weakened nothing. -/
theorem quasicentralApproximateUnitSeparable_of_monotone
    (h : MonotoneQuasicentralStatement) :
    QuasicentralApproximateUnitSeparableStatement := by
  intro H _ _ _ _ S
  obtain ⟨u, hq, -⟩ := h H S
  exact ⟨u.toFun, u.isCompact, u.isSelfAdjoint, u.norm_le, hq, u.tendsto_left⟩

end

end ShulmanFill
end GroupApproximation
