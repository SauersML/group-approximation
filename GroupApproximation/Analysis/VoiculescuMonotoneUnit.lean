import GroupApproximation.Analysis.VoiculescuQuasicentral
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# (V1c) The quasicentral approximate unit, positive and increasing

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

## The two model tests

`MonotoneCompactUnit.succ_sub` is the two-element-chain test, and it is stated in
the form the consumer needs rather than as a restatement of the hypothesis: the
successive difference is a positive compact contraction, which is exactly what
`(e_{j+1} - e_j)^{1/2}` requires of it.  A datum that recorded monotonicity but
not positivity, or positivity but not the upper bound, fails it.

`exists_monotoneCompactUnit_of_finiteDimensional` is the consistency test: on a
finite-dimensional space the constant unit `1` satisfies every clause at once,
so the conjunction is satisfiable and no clause contradicts another.  That is the
check a strengthened datum most needs, since strengthening is where clause sets
go inconsistent.

`quasicentralApproximateUnitSeparable_of_monotone` records that this is a genuine
strengthening of the landed (V1): it implies it, so nothing was weakened while
adding the order.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The strengthened datum -/

/-- **(V1c) A sequential approximate unit for the compacts that is positive and
increasing.**  The landed `SequentialCompactUnit` with the order clauses
Arveson's cut needs. -/
structure MonotoneCompactUnit (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] extends SequentialCompactUnit H where
  /-- Each member is positive. -/
  nonneg : ∀ n, 0 ≤ toFun n
  /-- Each member is dominated by the identity. -/
  le_one : ∀ n, toFun n ≤ 1
  /-- The members increase. -/
  mono : Monotone toFun

namespace MonotoneCompactUnit

variable (u : MonotoneCompactUnit H)

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

end MonotoneCompactUnit

/-! ## The statement -/

/-- **(V1c) as a statement.**  Every separable Hilbert space has a positive
increasing sequential approximate unit for its compacts that is asymptotically
central for a given countable family. -/
def MonotoneQuasicentralStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (S : ℕ → (H →L[ℂ] H)),
      ∃ u : MonotoneCompactUnit H,
        ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0)

/-! ## The model tests -/

/-- **The clause set is consistent.**  On a finite-dimensional space the constant
unit `1` satisfies every clause simultaneously: it is compact because the
identity of a finite-dimensional space is, it is positive and equal to its own
bound, it is trivially monotone, it commutes with everything exactly, and it
absorbs every operator exactly.  So the strengthened datum is inhabited and no
clause contradicts another. -/
theorem exists_monotoneCompactUnit_of_finiteDimensional (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H] (S : ℕ → (H →L[ℂ] H)) :
    ∃ u : MonotoneCompactUnit H,
      ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0) := by
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
  refine ⟨{ toFun := fun _ ↦ 1
            isCompact := fun _ ↦ hone
            isSelfAdjoint := fun _ ↦ IsSelfAdjoint.one _
            norm_le := fun _ ↦ hnorm
            tendsto_left := fun T _ ↦ ?_
            nonneg := fun _ ↦ zero_le_one
            le_one := fun _ ↦ le_rfl
            mono := monotone_const }, ?_⟩
  · refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [one_mul, sub_self, norm_zero]
  · intro k
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [one_mul, mul_one, sub_self, norm_zero]

/-- **The strengthening is a strengthening.**  The monotone statement implies the
landed (V1), so adding the order clauses weakened nothing. -/
theorem quasicentralApproximateUnitSeparable_of_monotone
    (h : MonotoneQuasicentralStatement) :
    QuasicentralApproximateUnitSeparableStatement := by
  intro H _ _ _ _ S
  obtain ⟨u, hq⟩ := h H S
  exact ⟨u.toFun, u.isCompact, u.isSelfAdjoint, u.norm_le, hq, u.tendsto_left⟩

end

end ShulmanFill
end GroupApproximation
