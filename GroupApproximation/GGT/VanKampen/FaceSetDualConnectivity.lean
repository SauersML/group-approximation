import GroupApproximation.GGT.VanKampen.FaceSetBoundaryExit

/-!
# The selected-face dual along a boundary cycle

The `BoundaryStep` relation already contains the internal-edge traversal of a
selected face set.  This file projects those steps to a finite dual-face
relation.  It proves that every two face occurrences on one
`FaceSetBoundary.cycle` lie in the same equivalence class of the selected-face
dual.  This is the dual-graph connectivity supplied by the estimating record;
it is the input for a spanning-tree/extremal-face argument.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqDual :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

/-- Two selected faces are adjacent when one ambient edge has these two faces
on its sides.  The selected-membership conjuncts make this the dual graph of
the chosen face set rather than the full map dual. -/
def SelectedFaceAdjacency
    (faces : Finset Delta.toCombMap.Face)
    (f g : Delta.toCombMap.Face) : Prop :=
  f ∈ faces ∧ g ∈ faces ∧
    ∃ d : Delta.toCombMap.Dart,
      Delta.toCombMap.faceOf d = f ∧
        Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = g

private theorem selectedFaceAdjacency_of_internalMove
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hmove : InternalBoundaryMove Delta faces d e) :
    SelectedFaceAdjacency faces
      (Delta.toCombMap.faceOf d) (Delta.toCombMap.faceOf e) := by
  rcases hmove with ⟨hd, hda, rfl⟩
  refine ⟨hd, ?_, ?_⟩
  · exact (by
      rw [Delta.toCombMap.faceOf_facePerm]
      exact hda)
  refine ⟨d, rfl, ?_⟩
  exact (Delta.toCombMap.faceOf_facePerm
    (Delta.toCombMap.alpha d)).symm

private theorem selectedFaceEqvGen_of_boundaryStep
    {faces : Finset Delta.toCombMap.Face}
    {d e : Delta.toCombMap.Dart}
    (hstep : BoundaryStep Delta faces d e) :
    Relation.EqvGen (SelectedFaceAdjacency faces)
      (Delta.toCombMap.faceOf d) (Delta.toCombMap.faceOf e) := by
  have hlift : Relation.ReflTransGen
      (SelectedFaceAdjacency faces)
      (Delta.toCombMap.faceOf (Delta.toCombMap.facePerm d))
      (Delta.toCombMap.faceOf e) := by
    apply hstep.2.2.lift (fun x => Delta.toCombMap.faceOf x)
    intro a b hab
    exact selectedFaceAdjacency_of_internalMove hab
  have hstart : Delta.toCombMap.faceOf
      (Delta.toCombMap.facePerm d) = Delta.toCombMap.faceOf d :=
    Delta.toCombMap.faceOf_facePerm d
  rw [hstart] at hlift
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ hlift

private theorem eqvGen_face_head_to_mem
    {R : Delta.toCombMap.Dart → Delta.toCombMap.Dart → Prop}
    {S : Delta.toCombMap.Face → Delta.toCombMap.Face → Prop}
    (hstep : ∀ {a b}, R a b →
      Relation.EqvGen S (Delta.toCombMap.faceOf a)
        (Delta.toCombMap.faceOf b))
    {cycle : List Delta.toCombMap.Dart}
    (hne : cycle ≠ []) (hchain : cycle.IsChain R)
    {d : Delta.toCombMap.Dart} (hd : d ∈ cycle) :
    Relation.EqvGen S
      (Delta.toCombMap.faceOf (cycle.head hne))
      (Delta.toCombMap.faceOf d) := by
  induction cycle with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
      by_cases hda : d = a
      · subst d
        exact Relation.EqvGen.refl _
      · have hdtail : d ∈ tail := by
          rcases List.mem_cons.mp hd with had | htail
          · exact (hda had).elim
          · exact htail
        cases tail with
        | nil => simp at hdtail
        | cons b tail =>
            have hab : R a b := by
              have hcons : List.IsChain R (a :: b :: tail) := by
                simpa only [List.cons_append] using hchain
              exact (List.isChain_cons_cons.mp hcons).1
            have htail : List.IsChain R (b :: tail) := hchain.tail
            have hhead : Relation.EqvGen S
                (Delta.toCombMap.faceOf b)
                (Delta.toCombMap.faceOf d) := by
              exact ih (by simp) htail hdtail
            exact Relation.EqvGen.trans _ _ _
              (hstep hab) hhead

/-- All boundary darts of a selected face set have face labels in one dual
equivalence class. -/
theorem boundaryCycle_faces_connected
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {d e : Delta.toCombMap.Dart}
    (hd : d ∈ boundary.cycle) (he : e ∈ boundary.cycle) :
    Relation.EqvGen (SelectedFaceAdjacency faces)
      (Delta.toCombMap.faceOf d) (Delta.toCombMap.faceOf e) := by
  have hhead_d := eqvGen_face_head_to_mem
    (S := SelectedFaceAdjacency faces)
    (fun h => selectedFaceEqvGen_of_boundaryStep h)
    boundary.cycle_nonempty boundary.cycle_chain hd
  have hhead_e := eqvGen_face_head_to_mem
    (S := SelectedFaceAdjacency faces)
    (fun h => selectedFaceEqvGen_of_boundaryStep h)
    boundary.cycle_nonempty boundary.cycle_chain he
  exact Relation.EqvGen.trans _ _ _ hhead_d.symm hhead_e

theorem boundaryCycle_face_mem
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    {d : Delta.toCombMap.Dart} (hd : d ∈ boundary.cycle) :
    Delta.toCombMap.faceOf d ∈ faces :=
  (boundary.cycle_mem_iff d).mp hd |>.1

end Embedded
end VanKampen
end GGT
end GroupApproximation
