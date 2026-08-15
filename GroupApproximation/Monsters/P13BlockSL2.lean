import GroupApproximation.Monsters.SL2Completeness
import GroupApproximation.Monsters.SL3BlockEmbedding

/-!
# The rank-two block inside P13

Completeness of the rank-two braid presentation upgrades the comparison
homomorphism `sl2ToP13 : SL2P →* P13` to an embedding: through the
commuting square `toSL3 ∘ sl2ToP13 = blockEmbed ∘ toSL2`, the composite
is injective, hence so is `sl2ToP13`.  The subgroup of `P13` generated
by the two corner roots `e₁₂, e₂₁` is therefore a faithful copy of
`SL₂(ℤ)`, mapped isomorphically by the matrix model onto the top-left
block — the first parabolic ingredient of the completeness programme
for `P13` itself.
-/

namespace GroupApproximation
namespace P13BlockSL2

open LiteralP13Presentation LiteralP13MatrixModel P13SteinbergCalculus
open SL2BraidPresentation
open P13SL2Comparison SL3BlockEmbedding SL2Completeness

noncomputable section

/-- The comparison homomorphism from the rank-two braid presentation
into `P13` is injective. -/
theorem sl2ToP13_injective : Function.Injective sl2ToP13 := by
  have hcomp : Function.Injective (toSL3.comp sl2ToP13) := by
    rw [toSL3_comp_sl2ToP13]
    intro g h hgh
    simp only [MonoidHom.comp_apply] at hgh
    exact toSL2_injective (blockEmbed_injective hgh)
  intro g h hgh
  apply hcomp
  simp only [MonoidHom.comp_apply, hgh]

/-- The matrix model is injective on the image of the rank-two
comparison: the block copy of `SL₂(ℤ)` sits faithfully inside `P13`. -/
theorem toSL3_injOn_blockRange {g h : SL2P}
    (heq : toSL3 (sl2ToP13 g) = toSL3 (sl2ToP13 h)) : g = h := by
  have hsq := congrArg (fun φ : SL2P →* SL3 => φ g) toSL3_comp_sl2ToP13
  have hsq' := congrArg (fun φ : SL2P →* SL3 => φ h) toSL3_comp_sl2ToP13
  simp only [MonoidHom.comp_apply] at hsq hsq'
  rw [hsq, hsq'] at heq
  exact toSL2_injective (blockEmbed_injective heq)

/-- An element of the block copy that the matrix model kills is
trivial. -/
theorem eq_one_of_blockRange_of_map_eq_one {g : SL2P}
    (h1 : toSL3 (sl2ToP13 g) = 1) : sl2ToP13 g = 1 := by
  have hg : g = 1 := by
    apply toSL3_injOn_blockRange
    rw [h1, map_one, map_one]
  rw [hg, map_one]

end

end P13BlockSL2
end GroupApproximation
