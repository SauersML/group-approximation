import GroupApproximation.Sofic.LiteralFinitePacketStarCollapse

/-!
# The literal finite-packet collapse statement

This is the manuscript-facing endpoint for the concrete affine star-packet
amalgam.  Its packet is the symmetric group on exactly nine sites.
-/

namespace GroupApproximation
namespace ManuscriptNonMF

open LiteralFinitePacketStarCollapse
open FinitePacketStarAmalgam

/-- The complete literal star-packet conclusion, with no supplied carrier,
packet, covariance datum, or analytic collapse hypothesis. -/
def PrintedLiteralFinitePacketCollapse : Prop :=
  alpha.range.index = 8 ∧
    Nat.card (Sites alpha) = 9 ∧
    ∀ B : OpAlmostRepresentation W,
      CoordinateCollapse alpha alpha_injective B

/-- The premise-free manuscript endpoint for the literal finite packet. -/
theorem manuscriptLiteralFinitePacketCollapse :
    PrintedLiteralFinitePacketCollapse :=
  ⟨alpha_range_index_eq_eight,
    packetDegree_eq_nine,
    manuscriptLiteralAffineStarPacketCollapse⟩

end ManuscriptNonMF
end GroupApproximation
