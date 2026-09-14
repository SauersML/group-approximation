import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceCycles
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionEuler
import GroupApproximation.GGT.VanKampen.CombMapInvariantRestrict
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Deleting a same-face bridge: the two sides

Let `a` be a dart of a connected map whose reverse lies on the same face, so its edge is a bridge.
Delete the edge (`EdgeDeletion.toCombMap`).  This module records how the deleted map sits in the
original one.
* `value_sigma`: vertex rotation of the deleted map, read through `EdgeDeletion.value`.
* `eqvGen_avoid_of_eqvGen`: a path of the deleted map is a path of moves that avoid the edge of `a`.
* `reach_or`: every dart of the deleted map is joined to `σ(α a)` (the successor of `a` on its face)
  or to `σ a` (the successor of `α a`), provided neither endpoint of the edge has degree one.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

namespace BridgeComponent

open Equiv

/-- **Erasing a point skips it once.** -/
theorem erase_val_eq {D : Type*} [DecidableEq D] (p : Perm D) (b : D) (y : {x : D // x ≠ b}) :
    (PermOrbitErasePoint.erase p b y).1 = if p y.1 = b then p b else p y.1 := by
  rw [PermOrbitErasePoint.erase_val, PermOrbitErasePoint.isolate, Perm.mul_apply, swap_apply_def]
  split_ifs with h1 h2
  · rfl
  · exact absurd (p.injective h2) y.2
  · rfl

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- **Vertex rotation after deleting the edge of `a`**, read in the original map. -/
theorem value_sigma (x : EdgeDeletion.Dart M a) :
    EdgeDeletion.value M a ((EdgeDeletion.toCombMap M a).sigma x) =
      if (if M.sigma (EdgeDeletion.value M a x) = a then M.sigma a
          else M.sigma (EdgeDeletion.value M a x)) = M.alpha a then
        (if M.sigma (M.alpha a) = a then M.sigma a else M.sigma (M.alpha a))
      else (if M.sigma (EdgeDeletion.value M a x) = a then M.sigma a
          else M.sigma (EdgeDeletion.value M a x)) := by
  change ((PermOrbitErasePoint.erase (PermOrbitErasePoint.erase M.sigma a)
    (EdgeDeletion.reverseDart M a) x).1).1 = _
  rw [erase_val_eq]
  have hx : (PermOrbitErasePoint.erase M.sigma a x.1).1 =
      if M.sigma (EdgeDeletion.value M a x) = a then M.sigma a
        else M.sigma (EdgeDeletion.value M a x) := erase_val_eq M.sigma a x.1
  have hr : (PermOrbitErasePoint.erase M.sigma a (EdgeDeletion.reverseDart M a)).1 =
      if M.sigma (M.alpha a) = a then M.sigma a else M.sigma (M.alpha a) :=
    erase_val_eq M.sigma a (EdgeDeletion.reverseDart M a)
  by_cases h : PermOrbitErasePoint.erase M.sigma a x.1 = EdgeDeletion.reverseDart M a
  · have h' := congrArg Subtype.val h
    change _ = M.alpha a at h'
    rw [hx] at h'
    rw [if_pos h, hr, if_pos h']
  · have h' : ¬ (if M.sigma (EdgeDeletion.value M a x) = a then M.sigma a
        else M.sigma (EdgeDeletion.value M a x)) = M.alpha a := fun h'' =>
      h (Subtype.ext (hx.trans h''))
    rw [if_neg h, hx, if_neg h']

/-- **A path of the deleted map avoids the edge.** -/
theorem eqvGen_avoid_of_adjacent {x y : EdgeDeletion.Dart M a}
    (h : (EdgeDeletion.toCombMap M a).Adjacent x y) :
    Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x)
      (EdgeDeletion.value M a y) := by
  have hcl : ∀ z, Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x) z →
      Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x) (M.sigma z) :=
    fun z hz => Relation.EqvGen.trans _ _ _ hz (Relation.EqvGen.rel _ _ (Or.inl rfl))
  have hrefl := Relation.EqvGen.refl (r := AvoidEdgeStep M a) (EdgeDeletion.value M a x)
  rcases h with h | h
  · have hv : EdgeDeletion.value M a y = M.alpha (EdgeDeletion.value M a x) := by
      rw [← h]
      exact EdgeDeletion.alpha_val M a x
    rw [hv]
    exact Relation.EqvGen.rel _ _ (Or.inr ⟨EdgeDeletion.value_ne M a x,
      EdgeDeletion.value_ne_reverse M a x, rfl⟩)
  · have hv := value_sigma M a x
    rw [h] at hv
    rw [hv]
    by_cases h1 : M.sigma (EdgeDeletion.value M a x) = a
    · have ha : Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x) a := by
        have := hcl _ hrefl
        rwa [h1] at this
      rw [if_pos h1]
      by_cases h2 : M.sigma a = M.alpha a
      · have hα : Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x) (M.alpha a) := by
          have := hcl _ ha
          rwa [h2] at this
        rw [if_pos h2]
        by_cases h3 : M.sigma (M.alpha a) = a
        · rw [if_pos h3]
          exact hcl _ ha
        · rw [if_neg h3]
          exact hcl _ hα
      · rw [if_neg h2]
        exact hcl _ ha
    · rw [if_neg h1]
      by_cases h2 : M.sigma (EdgeDeletion.value M a x) = M.alpha a
      · have hα : Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x) (M.alpha a) := by
          have := hcl _ hrefl
          rwa [h2] at this
        rw [if_pos h2]
        by_cases h3 : M.sigma (M.alpha a) = a
        · have ha : Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x) a := by
            have := hcl _ hα
            rwa [h3] at this
          rw [if_pos h3]
          exact hcl _ ha
        · rw [if_neg h3]
          exact hcl _ hα
      · rw [if_neg h2]
        exact hcl _ hrefl

/-- **Paths of the deleted map avoid the edge.** -/
theorem eqvGen_avoid_of_eqvGen {x y : EdgeDeletion.Dart M a}
    (h : Relation.EqvGen (EdgeDeletion.toCombMap M a).Adjacent x y) :
    Relation.EqvGen (AvoidEdgeStep M a) (EdgeDeletion.value M a x)
      (EdgeDeletion.value M a y) := by
  induction h with
  | rel x y h => exact eqvGen_avoid_of_adjacent M a h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

omit [DecidableEq M.Dart] in
/-- The successor of `a` on its face is not `a`. -/
theorem sigma_alpha_ne (hface : M.faceOf a = M.faceOf (M.alpha a)) : M.sigma (M.alpha a) ≠ a := by
  intro h
  have hfix : Function.IsFixedPt M.facePerm a := h
  exact M.alpha_fixedPointFree a (((M.faceOf_eq_iff _ _).mp hface).eq_of_left hfix).symm

omit [DecidableEq M.Dart] in
/-- The successor of `α a` on its face is not `α a`. -/
theorem sigma_ne_alpha (hface : M.faceOf a = M.faceOf (M.alpha a)) : M.sigma a ≠ M.alpha a := by
  intro h
  have hfix : Function.IsFixedPt M.facePerm (M.alpha a) := by
    show M.sigma (M.alpha (M.alpha a)) = M.alpha a
    rw [M.alpha_involutive]
    exact h
  exact M.alpha_fixedPointFree a (((M.faceOf_eq_iff _ _).mp hface).symm.eq_of_left hfix)

/-- The successor `σ (α a)` of `a` on its face, as a dart of the deleted map. -/
def near0 (hface : M.faceOf a = M.faceOf (M.alpha a)) (hstart : M.sigma (M.alpha a) ≠ M.alpha a) :
    EdgeDeletion.Dart M a :=
  EdgeDeletion.ofValue M a (M.sigma (M.alpha a)) (sigma_alpha_ne M a hface) hstart

/-- The successor `σ a` of `α a` on its face, as a dart of the deleted map. -/
def near1 (hface : M.faceOf a = M.faceOf (M.alpha a)) (htail : M.sigma a ≠ a) :
    EdgeDeletion.Dart M a :=
  EdgeDeletion.ofValue M a (M.sigma a) htail (sigma_ne_alpha M a hface)

end BridgeComponent

#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.erase_val_eq
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.value_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.eqvGen_avoid_of_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.sigma_alpha_ne
#audit_axioms GroupApproximation.GGT.VanKampen.BridgeComponent.sigma_ne_alpha

end GroupApproximation.GGT.VanKampen
