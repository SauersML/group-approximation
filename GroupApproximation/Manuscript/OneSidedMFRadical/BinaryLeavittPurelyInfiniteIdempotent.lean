import GroupApproximation.Manuscript.OneSidedMFRadical.PartialClosureAnalysis
import GroupApproximation.Algebra.PurelyInfiniteBridge

/-!
# The printed adjective, in the predicate the printed theorem consumes

`non_mf_groups_exist.tex` says "purely infinite simple" in two places about the
same ring, and until now the tree said it with two different predicates:

* the adjective, "the algebras `L_k(1,d)` are purely infinite simple", carried by
  `PartialClosureAnalysis.manuscriptPrintedBinaryLeavittPurelyInfiniteSimple` in
  the **sandwich** form `IsPurelyInfiniteSimpleUnitalRing`;
* the hypothesis of `thm:mf-quotient-units`, "let `R` be a countable purely
  infinite simple ring", which every carrier states in the **idempotent** form
  `IsPurelyInfiniteSimpleRing` of Ara--Goodearl--Pardo, Definitions 1.2.

One English phrase, two Lean predicates, no bridge: exactly the shape in which a
consumer picks up the wrong one and nothing goes red.  `Algebra/PurelyInfiniteBridge.lean`
supplies the bridge; this module spends it on the manuscript's own coefficient
ring, so that the printed adjective now discharges the printed hypothesis.

## What it spends

`isPurelyInfiniteSimpleRing_of_sandwich` needs simplicity, the sandwich clause,
and one proper isometry.  The first two are the first and third components of the
sandwich predicate, already proved.  The isometry is the printed Leavitt
relation: `t₀ * s₀ = 1` (`LeavittFamily.t0_s0`) with `s₀ * t₀ = p₀ ≠ 1`
(`printed_p_eq`, `printed_p0_ne_one`) — the same pair
`manuscriptPrintedBinaryLeavittPurelyInfiniteSimple` already uses to prove `R` is
not a division ring.  So nothing new about the ring is assumed: the isometry the
bridge asks for is a datum the printed proof was already spending.

The middle clause of the sandwich predicate — `R` is not a division ring — is
**not** used here, and is discarded by the `-` in the destructuring below.  It is
what the sandwich form needs to exclude the degenerate case; the idempotent form
excludes it through the isometry instead.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

/-- **The printed adjective for the manuscript's coefficient ring, in the
Ara--Goodearl--Pardo idempotent form.**

This is the proposition `thm:mf-quotient-units` takes as its hypothesis, at
`R = L_{𝔽₂}(1,2)`. -/
def PrintedBinaryLeavittPurelyInfiniteSimpleIdempotent : Prop :=
  GroupApproximation.MFQuotientUnits.IsPurelyInfiniteSimpleRing R

/-- The sandwich form of the printed adjective implies the idempotent form, on
the concrete coefficient ring, through the printed one-sided inverse. -/
theorem manuscriptBinaryLeavittPurelyInfiniteSimpleIdempotent :
    PrintedBinaryLeavittPurelyInfiniteSimpleIdempotent := by
  obtain ⟨hsimple, -, hsand⟩ := manuscriptPrintedBinaryLeavittPurelyInfiniteSimple
  have hst : leavittFamily.s0 * leavittFamily.t0 ≠ 1 := by
    rw [← printed_p_eq]
    exact printed_p0_ne_one
  exact GroupApproximation.MFQuotientUnits.isPurelyInfiniteSimpleRing_of_sandwich
    hsimple leavittFamily.t0_s0 hst hsand

end OneSidedMFRadical
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptBinaryLeavittPurelyInfiniteSimpleIdempotent
