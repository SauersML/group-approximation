import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.ApproxInvolutionCorner
import GroupApproximation.Sofic.KazhdanCornerPolar

/-!
# An MF regular character forces the group to be operator MF

The definitional surface of Shulman's MF-trace condition, specialized to
the regular character of a countable group, and the recognition theorem:
if the regular character admits matrix models that are asymptotically
multiplicative, asymptotically star-preserving, pointwise bounded, and
trace-correct in operator norm, then the group itself is operator MF with
separation constant `1`.

The mechanism, following `research/regular-character-mf-trace-implies-
group-mf-proof.md`: the trace clause at `1` pins a macroscopic unit
corner, obtained by spectral rounding of the hermitian part of the image
of `1`; inflating the cornered images by the corner complement produces
full near-unitaries, which polar-correct to exact unitaries; and the
trace clause at `g ≠ 1` makes the corrected unitaries separate at
Hilbert–Schmidt distance `√2`, which the operator norm dominates.

The two analytic bricks are already in the library: quantitative
involution rounding (`ApproxInvolutionCorner`) and quantitative polar
correction under a Gram-defect bound (`KazhdanCornerPolar`).

**Status: statement-complete; the quantitative assembly is in progress.**
This module is not yet imported by the library root.
-/

namespace GroupApproximation
namespace MFTraceRecognition

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable (G : Type u) [Group G]

/-- A finite-test-set matrix model of the regular character: operator-norm
multiplicativity, star-compatibility, and trace-correctness on the test
set, with a pointwise norm bound.  This is the local form of Shulman's
MF-trace condition for the canonical trace of the full group
`C^*`-algebra, restricted to the group unitaries. -/
structure RegularCharacterModel (F : Finset G) (ε : ℝ) (B : G → ℝ) where
  /-- The finite model space. -/
  carrier : FiniteModel
  /-- The model space is nonempty. -/
  nonempty : 0 < Fintype.card carrier
  /-- The matrix images of the group elements. -/
  map : G → Matrix carrier carrier ℂ
  /-- Pointwise norm bound, uniform over the accuracy parameter. -/
  bounded : ∀ g ∈ F, ‖map g‖ ≤ B g
  /-- Operator-norm multiplicativity on the test set. -/
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, ‖map (g * h) - map g * map h‖ ≤ ε
  /-- Star-compatibility on the test set. -/
  star_compatible : ∀ g ∈ F, ‖map g⁻¹ - (map g)ᴴ‖ ≤ ε
  /-- Trace-correctness: the normalized trace approximates the regular
  character. -/
  trace_correct : ∀ g ∈ F,
    ‖(Matrix.trace (map g)) / (Fintype.card carrier : ℂ) -
      (if g = 1 then 1 else 0)‖ ≤ ε

/-- The regular character of `G` is an MF trace: models exist at every
finite test set and accuracy, with a pointwise bound independent of the
accuracy. -/
def IsMFRegularCharacter : Prop :=
  ∃ B : G → ℝ, ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    Nonempty (RegularCharacterModel G F ε B)

/-- **MF-trace recognition.**  If the regular character of a group is an
MF trace, the group is operator MF: the corner-and-polar correction of
any trace-correct model family produces operator-norm local models with
separation constant `1`.

The trace clause does all the work the weak definition cannot: at `1` it
pins the unit corner at relative dimension one, and at `g ≠ 1` it gives
separation `√2 - o(1) > 1` automatically. -/
theorem isNormApproximable_of_isMFRegularCharacter
    (h : IsMFRegularCharacter G) : IsNormApproximable G 1 := by
  sorry

end MFTraceRecognition
end GroupApproximation
