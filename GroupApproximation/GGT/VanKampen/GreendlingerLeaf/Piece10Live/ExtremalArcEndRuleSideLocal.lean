import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndSurgery
import GroupApproximation.Meta.AxiomGuard

/-!
# Case (B) of the arc-end surgery rule: the local translation

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-28.

For a dart `y` whose face lies in `K.faces` ("inside"), the kept predicate
`P10ExtremalResidual.keptPred K y` on the walk `K.boundary.cycle` is the complement of the face
class of `y`: a walk dart `x` has its face in `K.faces` and the far face `alpha x` outside, and a
face class lies on one side of `K.faces` (`extremalArcEndSurgery_mem_faces_iff`), so the class of
`y` never meets `alpha x`.  Proved here:

* `extremalArcEndRuleSide_kept_iff`, `extremalArcEndRuleSide_removed_iff`: kept iff outside the
  class, removed iff inside it;
* `extremalArcEndRuleSide_removed_eq_zero_iff`: count `0` iff the class contains no arc dart
  (`ExtremalArcEndRuleSideArcFree`);
* `extremalArcEndRuleSide_choice_iff`: `ExtremalClassChoice` iff the class avoids the face of a
  relator cell in `K.faces` (`ExtremalArcEndRuleSideCellFree`); the exterior and source clauses
  hold since both faces are outside `K.faces`;
* `extremalArcEndRuleSide_linkedRuns_iff`: `ExtremalMinimalLinkedRuns` iff the class form
  `ExtremalArcEndRuleSideLinked`;
* `extremalArcEndRuleSide_side_inside`: a side dart is inside;
* `extremalArcEndRuleSide_inside`: with no extra exterior class, a choice class is inside.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section RuleSideLocal

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Arc free**: the class of `y` contains no dart of the target arc or reversed source arc. -/
def ExtremalArcEndRuleSideArcFree (K : PocketFaceSet D eps X lo hi) (y : X.toCombMap.Dart) :
    Prop :=
  ∀ x ∈ K.targetArc.darts ++ invDarts X K.sourceArc.darts, ¬Relation.EqvGen
    (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y x

/-- **Cell free**: the class of `y` avoids the face of some relator cell of `K.faces`. -/
def ExtremalArcEndRuleSideCellFree (K : PocketFaceSet D eps X lo hi) (y : X.toCombMap.Dart) :
    Prop :=
  ∃ c : Fin X.rCellCount, (cell X c).face ∈ K.faces ∧
    ∀ x, X.toCombMap.faceOf x = (cell X c).face → ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y x

/-- **Linked runs, class form**: two walk darts outside the class of `y`, separated by a nonempty
run of walk darts inside it, have linked ends. -/
def ExtremalArcEndRuleSideLinked (K : PocketFaceSet D eps X lo hi) (y : X.toCombMap.Dart) :
    Prop :=
  ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
    K.boundary.cycle = A ++ d :: (B ++ e :: C) →
      ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y d →
      ¬Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y e →
      (∀ x ∈ B, Relation.EqvGen
        (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y x) →
      B ≠ [] → X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e

/-- **Kept iff outside the class**, for an inside `y` and a walk dart `x`. -/
theorem extremalArcEndRuleSide_kept_iff (K : PocketFaceSet D eps X lo hi)
    {y x : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ K.faces)
    (hx : x ∈ K.boundary.cycle) :
    P10ExtremalResidual.keptPred K y x = true ↔ ¬Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y x := by
  constructor
  · intro hk hyx
    have h1 := ((movePred_eq_true_iff X.toCombMap
      (regionColour X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) y) x).mp hk).1
    rw [(regionColour_eq_true_iff X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) y
      x).mpr hyx] at h1
    exact absurd h1 (by decide)
  · intro hyx
    refine extremalArcEndSurgery_kept_of_not K y x hyx (fun hya => ?_)
    exact ((K.boundary.cycle_mem_iff x).mp hx).2
      ((extremalArcEndSurgery_mem_faces_iff K hya).mp hy)

/-- **Removed iff inside the class**, for an inside `y` and a walk dart `x`. -/
theorem extremalArcEndRuleSide_removed_iff (K : PocketFaceSet D eps X lo hi)
    {y x : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ K.faces)
    (hx : x ∈ K.boundary.cycle) :
    P10ExtremalResidual.keptPred K y x = false ↔ Relation.EqvGen
      (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) y x := by
  constructor
  · intro hf
    by_contra hn
    have hk := (extremalArcEndRuleSide_kept_iff K hy hx).mpr hn
    rw [hf] at hk
    exact absurd hk (by decide)
  · intro hr
    cases hb : P10ExtremalResidual.keptPred K y x with
    | false => rfl
    | true => exact absurd hr ((extremalArcEndRuleSide_kept_iff K hy hx).mp hb)

/-- **An arc dart lies on the walk.** -/
theorem extremalArcEndRuleSide_arc_mem_cycle (K : PocketFaceSet D eps X lo hi)
    {x : X.toCombMap.Dart} (hx : x ∈ K.targetArc.darts ++ invDarts X K.sourceArc.darts) :
    x ∈ K.boundary.cycle := by
  rw [K.decomposition]
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inr h)
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr h)))))

/-- **A side dart is inside**: it lies on the walk, so its face is in `K.faces`. -/
theorem extremalArcEndRuleSide_side_inside (K : PocketFaceSet D eps X lo hi)
    {y : X.toCombMap.Dart} (hy : y ∈ K.firstSide ++ K.secondSide) :
    X.toCombMap.faceOf y ∈ K.faces := by
  have hyc : y ∈ K.boundary.cycle := by
    rw [K.decomposition]
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
        (List.mem_append.mpr (Or.inl h)))))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
  exact ((K.boundary.cycle_mem_iff y).mp hyc).1

/-- **Count `0` iff arc free**, for an inside `y`. -/
theorem extremalArcEndRuleSide_removed_eq_zero_iff (K : PocketFaceSet D eps X lo hi)
    {y : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ K.faces) :
    ExtremalArcEndRemoved K y = 0 ↔ ExtremalArcEndRuleSideArcFree K y := by
  constructor
  · intro h0 x hx
    unfold ExtremalArcEndRemoved at h0
    obtain ⟨hT, hS⟩ := Nat.add_eq_zero_iff.mp h0
    have hk : P10ExtremalResidual.keptPred K y x = true := by
      rcases List.mem_append.mp hx with h | h
      · exact extremalArcEnd_kept_of_countP_eq_zero K y hT x h
      · exact extremalArcEnd_kept_of_countP_eq_zero K y hS x h
    exact (extremalArcEndRuleSide_kept_iff K hy (extremalArcEndRuleSide_arc_mem_cycle K hx)).mp hk
  · intro h
    have hk : ∀ x ∈ K.targetArc.darts ++ invDarts X K.sourceArc.darts,
        P10ExtremalResidual.keptPred K y x = true := fun x hx =>
      (extremalArcEndRuleSide_kept_iff K hy (extremalArcEndRuleSide_arc_mem_cycle K hx)).mpr
        (h x hx)
    unfold ExtremalArcEndRemoved
    refine Nat.add_eq_zero_iff.mpr ⟨List.countP_eq_zero.mpr ?_, List.countP_eq_zero.mpr ?_⟩
    · intro x hx
      simp [hk x (List.mem_append.mpr (Or.inl hx))]
    · intro x hx
      simp [hk x (List.mem_append.mpr (Or.inr hx))]

/-- **Choice iff cell free**, for an inside `y`: the exterior and source faces are outside
`K.faces`, so the class of `y` avoids them. -/
theorem extremalArcEndRuleSide_choice_iff (K : PocketFaceSet D eps X lo hi)
    {y : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ K.faces) :
    ExtremalClassChoice K y ↔ ExtremalArcEndRuleSideCellFree K y := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    refine ⟨Or.inr ?_, Or.inr ?_, h⟩
    · intro x hx hyx
      have hm := (extremalArcEndSurgery_mem_faces_iff K hyx).mp hy
      rw [hx] at hm
      exact K.outerFace_not_mem hm
    · intro x hx hyx
      have hm := (extremalArcEndSurgery_mem_faces_iff K hyx).mp hy
      rw [hx] at hm
      exact K.source_not_mem hm

/-- **Linked runs iff the class form**, for an inside `y`. -/
theorem extremalArcEndRuleSide_linkedRuns_iff (K : PocketFaceSet D eps X lo hi)
    {y : X.toCombMap.Dart} (hy : X.toCombMap.faceOf y ∈ K.faces) :
    ExtremalMinimalLinkedRuns K y ↔ ExtremalArcEndRuleSideLinked K y := by
  constructor
  · intro h A d B e C hc hd he hB hne
    have hdc : d ∈ K.boundary.cycle := by rw [hc]; simp
    have hec : e ∈ K.boundary.cycle := by rw [hc]; simp
    refine h A d B e C hc ((extremalArcEndRuleSide_kept_iff K hy hdc).mpr hd)
      ((extremalArcEndRuleSide_kept_iff K hy hec).mpr he) (fun x hx => ?_) hne
    have hxc : x ∈ K.boundary.cycle := by rw [hc]; simp [hx]
    exact (extremalArcEndRuleSide_removed_iff K hy hxc).mpr (hB x hx)
  · intro h A d B e C hc hd he hB hne
    have hdc : d ∈ K.boundary.cycle := by rw [hc]; simp
    have hec : e ∈ K.boundary.cycle := by rw [hc]; simp
    refine h A d B e C hc ((extremalArcEndRuleSide_kept_iff K hy hdc).mp hd)
      ((extremalArcEndRuleSide_kept_iff K hy hec).mp he) (fun x hx => ?_) hne
    have hxc : x ∈ K.boundary.cycle := by rw [hc]; simp [hx]
    exact (extremalArcEndRuleSide_removed_iff K hy hxc).mp (hB x hx)

/-- **With no extra exterior class, a choice class is inside**: otherwise its two avoidance
clauses make it an extra exterior class. -/
theorem extremalArcEndRuleSide_inside (K : PocketFaceSet D eps X lo hi)
    {r : X.toCombMap.Dart} (hno : ∀ z, ¬ExtremalArcEndSurgeryExtraOut K z)
    (hr : ExtremalClassChoice K r) : X.toCombMap.faceOf r ∈ K.faces := by
  obtain ⟨hout, hsrc, -⟩ := hr
  by_contra hf
  refine hno r ⟨hf, ?_, ?_⟩
  · rcases hout with ⟨e, he, hk⟩ | hout
    · exact P10ExtremalBlock.outerAvoid_of_keptTarget K r he hk
    · exact hout
  · rcases hsrc with ⟨e, he, hk⟩ | hsrc
    · exact sourceAvoid_of_keptSource K r he hk
    · exact hsrc

end RuleSideLocal

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSideArcFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSideCellFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSideLinked
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_kept_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_removed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_arc_mem_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_side_inside
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_removed_eq_zero_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_choice_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_linkedRuns_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_inside
