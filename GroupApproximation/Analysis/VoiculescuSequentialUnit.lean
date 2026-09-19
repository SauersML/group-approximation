import GroupApproximation.Analysis.CalkinSchauderProof
import GroupApproximation.Analysis.VoiculescuQuasicentralStatement

/-!
# (V1a) A sequential approximate unit for the compacts

`ShulmanFill.QuasicentralApproximateUnitSeparableStatement` asks for a
*sequence* of compacts that absorbs every compact operator.
`Analysis/CStarIdealApproximateUnit` supplies an approximate unit for every
closed star-stable two-sided ideal, but it is a NET: an `IdealApproximateUnit`
is a filter datum, and its absorption clause is a `Tendsto` along that filter.
Turning the net into a sequence is exactly what `[SeparableSpace H]` pays for —
`K(H)` is σ-unital precisely when `H` is separable, which is the same fact as
the refutation recorded in `Analysis/VoiculescuQuasicentralStatement`, seen from
the other side.

This module isolates that leaf: the output as one structure for (V1b) to bind,
the orientation swap, and the reduction of the construction to a single
classical analytic step.

## The construction, and the one step it rests on

Not through the net at all.  Take a dense sequence in the separable `H` and let
`P n` be the orthogonal projection onto the span of its first `n` terms: finite
rank, hence compact, self-adjoint, of norm at most one, and `P n → 1` strongly.
For a compact `T` the image of the unit ball is totally bounded, and strong
convergence is uniform on totally bounded sets, so `‖T - P n * T‖ → 0`.

That last implication is the whole analytic content of (V1a) and is stated here
as `StrongToNormOnCompactsStatement` rather than assumed silently.  It is the
same fact family the lane will meet again in (V1b) — where the defect vector's
`0`-in-the-weak-closure step wants that a compact operator carries weakly null
sequences to norm null ones — so it is worth building once, well, at whichever
leaf reaches it first.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **The output of (V1a)**, as one datum: a sequence of compacts absorbing the
compacts from both sides.  (V1b) binds this rather than five clauses. -/
structure SequentialCompactUnit (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The members of the sequence. -/
  toFun : ℕ → (H →L[ℂ] H)
  /-- Each is compact. -/
  isCompact : ∀ n, IsCompactOperator (toFun n)
  /-- Each is self-adjoint. -/
  isSelfAdjoint : ∀ n, IsSelfAdjoint (toFun n)
  /-- Each is a contraction. -/
  norm_le : ∀ n, ‖toFun n‖ ≤ 1
  /-- It absorbs every compact operator on the left. -/
  tendsto_left : ∀ T : H →L[ℂ] H, IsCompactOperator T →
    Tendsto (fun n ↦ ‖T - toFun n * T‖) atTop (𝓝 0)

/-- **The orientation swap.**  For a self-adjoint unit the right-handed
absorption is the left-handed one at the adjoint, since taking adjoints is an
isometry and Schauder's theorem
(`CalkinAlgebra.isCompactOperator_star`) keeps compactness.  Stated on its
own because (V1b) wants both orientations. -/
theorem SequentialCompactUnit.tendsto_right (u : SequentialCompactUnit H)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    Tendsto (fun n ↦ ‖T - T * u.toFun n‖) atTop (𝓝 0) := by
  have hstar : ∀ n : ℕ,
      ‖T - T * u.toFun n‖ = ‖star T - u.toFun n * star T‖ := by
    intro n
    rw [← norm_star, star_sub, star_mul, (u.isSelfAdjoint n).star_eq]
  refine Tendsto.congr (fun n ↦ (hstar n).symm) ?_
  exact u.tendsto_left (star T) (CalkinAlgebra.isCompactOperator_star hT)

/-- **The analytic step (V1a) rests on**: against a compact operator, strong
convergence to the identity is norm convergence.

Stated as a named Prop rather than assumed inside the construction, because the
lane meets the same fact again in (V1b) and it should be built once. -/
def StrongToNormOnCompactsStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ℕ → (H →L[ℂ] H)), (∀ n, ‖P n‖ ≤ 1) →
      (∀ v : H, Tendsto (fun n ↦ P n v) atTop (𝓝 v)) →
      ∀ T : H →L[ℂ] H, IsCompactOperator T →
        Tendsto (fun n ↦ ‖T - P n * T‖) atTop (𝓝 0)

end

end ShulmanFill
end GroupApproximation
