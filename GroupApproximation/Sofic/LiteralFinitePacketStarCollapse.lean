import GroupApproximation.Sofic.FinitePacketStarAmalgam
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralAffineRangeIndexEight

/-!
# The literal affine star-packet collapse

This file specializes the finite star-packet amalgam to conjugation by the
doubling matrix in the literal affine group.  The carrier, packet action,
ascending-HNN factor, amalgam, and analytic collapse theorem have no inputs.

The compressed range has index eight, so the packet has exactly nine sites.
The index calculation is independent of the analytic collapse theorem.
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

/-- The literal compressed range has index eight. -/
theorem alpha_range_index_eq_eight : alpha.range.index = 8 :=
  LiteralAffineRangeIndexEight.conjD_range_index_eq_eight

/-- The literal packet has exactly nine sites. -/
theorem packetDegree_eq_nine : Nat.card (Sites alpha) = 9 :=
  packetDegree_eq_nine_iff_index_eq_eight.mpr alpha_range_index_eq_eight

/-- The same cardinality in the packet's chosen `Fintype` structure. -/
theorem packetFintypeCard_eq_nine : Fintype.card (Sites alpha) = 9 := by
  rw [← Nat.card_eq_fintype_card]
  exact packetDegree_eq_nine

/-- A fixed enumeration of the nine packet sites. -/
noncomputable def siteEquivFinNine : Sites alpha ≃ Fin 9 :=
  Fintype.equivFinOfCardEq packetFintypeCard_eq_nine

/-- The literal packet is the symmetric group `S₉`. -/
noncomputable def packetEquivS9 : Sigma ≃* Equiv.Perm (Fin 9) :=
  { siteEquivFinNine.permCongr with
    map_mul' := by
      intro p q
      ext i
      simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }

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
