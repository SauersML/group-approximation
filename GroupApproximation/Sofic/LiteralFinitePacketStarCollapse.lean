import GroupApproximation.Sofic.FinitePacketStarAmalgam
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge

/-!
# The literal affine star-packet collapse

This file specializes the finite star-packet amalgam to conjugation by the
doubling matrix in the literal affine group.  The carrier, packet action,
ascending-HNN factor, amalgam, and analytic collapse theorem have no inputs.

The available arithmetic proves that the packet has one more site than the
index of the compressed range.  Consequently its degree is nine exactly when
that index is eight.  The latter equality is kept as a separate arithmetic
statement; it is not an input to the collapse theorem.
-/

namespace GroupApproximation
namespace LiteralFinitePacketStarCollapse

open FinitePacketStarAmalgam

noncomputable section

/-- The literal affine base group. -/
abbrev Gamma : Type := ExplicitLinearModel.gammaBar

/-- Conjugation by the doubling matrix. -/
abbrev alpha : Gamma →* Gamma := LiteralNonMFLinearWitness.alpha

/-- The literal doubling endomorphism is injective. -/
theorem alpha_injective : Function.Injective alpha :=
  ExplicitLinearModel.conjD_injective

/-- The literal affine group has property `(T)`. -/
theorem gamma_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Gamma :=
  HasKazhdanPropertyT.of_mulEquiv
    LiteralBaseCompleteness.baseAffineEquiv.symm
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

/-- The concrete group
`(Sym(Gamma / alpha(Gamma) + {*}) semidirect Gamma) *_Gamma HNN(Gamma,alpha)`.
-/
abbrev W : Type :=
  Carrier alpha alpha_injective

/-- The finite packet in the literal carrier. -/
abbrev Sigma : Type := Packet alpha

/-- The packet degree is the compressed-range index plus the fixed star. -/
theorem packetDegree_eq_index_add_one :
    Nat.card (Sites alpha) = alpha.range.index + 1 := by
  change Nat.card ((Gamma ⧸ alpha.range) ⊕ Unit) =
    alpha.range.index + 1
  have hunit : Nat.card Unit = 1 := Nat.card_unique
  rw [Nat.card_sum, hunit, Subgroup.index_eq_card]

/-- The exact remaining arithmetic bridge to the nine-point packet. -/
theorem packetDegree_eq_nine_iff_index_eq_eight :
    Nat.card (Sites alpha) = 9 ↔ alpha.range.index = 8 := by
  rw [packetDegree_eq_index_add_one]
  omega

/-- **Premise-free literal affine star-packet collapse.**  Every
operator-norm almost representation of the concrete amalgam has, along a
cofinal subsequence, exact finite packet lifts whose generating star
transpositions all agree with the root star transposition. -/
theorem manuscriptLiteralAffineStarPacketCollapse
    (B : OpAlmostRepresentation W) :
    CoordinateCollapse alpha alpha_injective B :=
  coordinateCollapse alpha alpha_injective gamma_hasKazhdanPropertyT B

end

end LiteralFinitePacketStarCollapse
end GroupApproximation
