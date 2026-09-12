import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionDegenerate
import GroupApproximation.Meta.AxiomGuard

/-!
# Word values for the O52 surgery

The group algebra and the dart-list values used by the O52 surgery at least area
(`Estimating/OsinAppendixO52Surgery.lean`).

* `o52_mergedValue_eq_one`: after the two edge deletions the merged face reads `1`
  exactly when the non-cancellation clause of O52 fails.
* `Embedded.CyclicArc.reverseDarts_eq_cons`: the reversed arc starts at the reverse of
  the last dart of the arc.
* `Embedded.listVal_dartWord_darts`, `Embedded.listVal_dartWord_rotated`,
  `Embedded.listVal_revInv_rotate`: values of an arc, of its rotated carrier, and of
  the inverse carrier.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC

universe u w v

/-- **The merged word of the O52 surgery reads `1`.** -/
theorem o52_mergedValue_eq_one {G : Type*} [Group G] (A a₁ s' B a₂ t' r l : G)
    (F1 : (A * a₁)⁻¹ * r * (B * a₂)⁻¹ * l = 1)
    (F2 : (B * a₂)⁻¹ * t'⁻¹ = r⁻¹ * (A * a₁ * s') * r) :
    B⁻¹ * l * (s' * A) * (A⁻¹ * r) * (t' * B) = 1 := by
  have hl : l = B * a₂ * r⁻¹ * (A * a₁) := by
    calc l = (B * a₂ * r⁻¹ * (A * a₁)) * ((A * a₁)⁻¹ * r * (B * a₂)⁻¹ * l) := by group
      _ = B * a₂ * r⁻¹ * (A * a₁) := by rw [F1, mul_one]
  have hF2 : A * a₁ * s' = r * ((B * a₂)⁻¹ * t'⁻¹) * r⁻¹ := by
    rw [F2]
    group
  calc B⁻¹ * l * (s' * A) * (A⁻¹ * r) * (t' * B)
      = a₂ * r⁻¹ * (A * a₁ * s') * r * t' * B := by
        rw [hl]
        group
    _ = a₂ * r⁻¹ * (r * ((B * a₂)⁻¹ * t'⁻¹) * r⁻¹) * r * t' * B := by rw [hF2]
    _ = 1 := by group

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A cyclic arc of positive length has darts. -/
theorem CyclicArc.darts_ne_nil_of_length_pos {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) (h : 0 < arc.length) : arc.darts ≠ [] := by
  intro h'
  have hlen := arc.darts_length
  rw [h', List.length_nil] at hlen
  omega

/-- The reversed arc starts at the reverse of the last dart of the arc. -/
theorem CyclicArc.reverseDarts_eq_cons {M : CombMap.{v}} {cycle : List M.Dart}
    (arc : CyclicArc cycle) (h : arc.darts ≠ []) :
    arc.reverseDarts =
      M.alpha (arc.darts.getLast h) :: arc.darts.dropLast.reverse.map M.alpha := by
  unfold CyclicArc.reverseDarts
  conv_lhs => rw [← List.dropLast_append_getLast h]
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]

/-- The value of an arc splits off its last dart. -/
theorem listVal_dartWord_darts {Delta : DiscDiagram.{u, w, v} W}
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) (h : arc.darts ≠ []) :
    RelLetter.listVal (dartWord Delta arc.darts) =
      RelLetter.listVal (dartWord Delta arc.darts.dropLast) *
        (Delta.label (arc.darts.getLast h)).val := by
  conv_lhs => rw [← List.dropLast_append_getLast h]
  rw [dartWord_append, RelWord.listVal_append]
  congr 1
  show RelLetter.listVal [Delta.label (arc.darts.getLast h)] = _
  rw [RelWord.listVal_cons, RelLetter.listVal_nil, mul_one]

/-- The rotated carrier reads the arc, then the rest of the carrier. -/
theorem listVal_dartWord_rotated {Delta : DiscDiagram.{u, w, v} W}
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    RelLetter.listVal (dartWord Delta arc.rotated) =
      RelLetter.listVal (dartWord Delta arc.darts) *
        RelLetter.listVal (dartWord Delta (arc.rotated.drop arc.length)) := by
  rw [← RelWord.listVal_append, ← dartWord_append]
  exact congrArg (fun L => RelLetter.listVal (dartWord Delta L))
    (List.take_append_drop arc.length arc.rotated).symm

/-- The inverse carrier reads the inverse arc, then the inverse of the rest. -/
theorem listVal_revInv_rotate {Delta : DiscDiagram.{u, w, v} W}
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    RelLetter.listVal ((RelWord.revInv (dartWord Delta arc.rotated)).rotate
        (dartWord Delta (arc.rotated.drop arc.length)).length) =
      (RelLetter.listVal (dartWord Delta arc.darts))⁻¹ *
        (RelLetter.listVal (dartWord Delta (arc.rotated.drop arc.length)))⁻¹ := by
  have hsplit : dartWord Delta arc.rotated =
      dartWord Delta arc.darts ++ dartWord Delta (arc.rotated.drop arc.length) := by
    rw [← dartWord_append]
    exact congrArg (dartWord Delta) (List.take_append_drop arc.length arc.rotated).symm
  rw [hsplit, RelWord.revInv_append,
    ← RelWord.length_revInv (dartWord Delta (arc.rotated.drop arc.length)),
    List.rotate_append_length_eq, RelWord.listVal_append, RelWord.listVal_revInv,
    RelWord.listVal_revInv]

end Embedded

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.o52_mergedValue_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.reverseDarts_eq_cons
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_dartWord_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_dartWord_rotated
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_revInv_rotate
