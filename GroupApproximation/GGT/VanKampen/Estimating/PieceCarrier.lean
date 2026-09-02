import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge

/-!
# The value of the reversed target carrier

`Contiguity.targetInverseCarrier` is a *rotation* of `RelWord.revInv` of the
target arc's rotated cell word, and a rotation changes `GGT.RelLetter.listVal`
by conjugation (`HullSC.RelWord.listVal_rotate`).  So an alignment identity for
the arc word does not by itself identify the carrier's value, which is the one
piece of bookkeeping between the O52 certificate and
`Embedded.ReducedCellPieceBridge.of_cellContiguity`.

This module does that bookkeeping once.  Writing the target cell's boundary,
rotated to the arc's base, as `arc ++ rest`, the carrier reads the cell
backwards starting where the arc ends, so its value is `(rest * arc)⁻¹`.  That
is `listVal_targetInverseCarrier`.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
  {faces : Finset Delta.toCombMap.Face}

/-! ## Dart words commute with the list operations -/

theorem dartWord_length (darts : List Delta.toCombMap.Dart) :
    (dartWord Delta darts).length = darts.length := by
  simp only [dartWord, List.length_map]

theorem dartWord_take (darts : List Delta.toCombMap.Dart) (n : ℕ) :
    dartWord Delta (darts.take n) = (dartWord Delta darts).take n := by
  simp only [dartWord, List.map_take]

theorem dartWord_drop (darts : List Delta.toCombMap.Dart) (n : ℕ) :
    dartWord Delta (darts.drop n) = (dartWord Delta darts).drop n := by
  simp only [dartWord, List.map_drop]

/-! ## The carrier value -/

/-- **The reversed target carrier reads the cell backwards from the end of the
arc.**  With the target cell's boundary rotated to the arc's base and split as
`arc ++ rest`, the carrier's value is `(rest * arc)⁻¹`. -/
theorem listVal_targetInverseCarrier
    (Gamma : Contiguity D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) =
      (GGT.RelLetter.listVal (dartWord Delta
          ((Gamma.targetArcAtSome target htarget).rotated.drop
            (Gamma.targetArcAtSome target htarget).length)) *
        GGT.RelLetter.listVal (dartWord Delta
          (Gamma.targetArcAtSome target htarget).darts))⁻¹ := by
  classical
  have harc : (Gamma.targetArcAtSome target htarget).darts =
      (Gamma.targetArcAtSome target htarget).rotated.take
        (Gamma.targetArcAtSome target htarget).length := rfl
  have hle : (Gamma.targetArcAtSome target htarget).length ≤
      (dartWord Delta (Gamma.targetArcAtSome target htarget).rotated).length := by
    rw [dartWord_length, CyclicArc.rotated_length]
    exact (Gamma.targetArcAtSome target htarget).length_le
  -- abbreviations
  set A := Gamma.targetArcAtSome target htarget with hA
  set w := dartWord Delta A.rotated with hw
  set L := A.length with hL
  have hdroplen : (dartWord Delta (A.rotated.drop L)).length = w.length - L := by
    rw [dartWord_drop, List.length_drop]
  have hsplit : GGT.RelLetter.listVal w =
      GGT.RelLetter.listVal (w.take L) * GGT.RelLetter.listVal (w.drop L) := by
    conv_lhs => rw [← List.take_append_drop L w]
    rw [RelWord.listVal_append]
  have hrevlen : (RelWord.revInv w).length = w.length := by
    simp [RelWord.revInv]
  have hrotk : (w.length - L) ≤ (RelWord.revInv w).length := by
    rw [hrevlen]
    omega
  have hcarrier : Gamma.targetInverseCarrier target htarget =
      (RelWord.revInv w).rotate (w.length - L) := by
    rw [Contiguity.targetInverseCarrier, ← hw, ← hA, ← hL, hdroplen]
  rw [hcarrier, RelWord.listVal_rotate _ hrotk, RelWord.listVal_revInv]
  have hsub : w.length - (w.length - L) = L := Nat.sub_sub_self hle
  have htake : (RelWord.revInv w).take (w.length - L) =
      RelWord.revInv (w.drop L) := by
    simp only [RelWord.revInv, List.take_reverse, List.length_map, hsub,
      ← List.map_drop]
  rw [htake, RelWord.listVal_revInv, dartWord_drop, harc, dartWord_take,
    hsplit]
  group

end Embedded
end VanKampen
end GGT
end GroupApproximation
