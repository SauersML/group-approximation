import GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision
import GroupApproximation.GGT.VanKampen.DartExpansionVertices

/-! # Every edge away from the subdivided edge is retained as one actual dart -/

namespace GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.Output

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {Delta : DiscDiagram.{u, w, v} W} {a : Delta.toCombMap.Dart}
  {word : List (RelLetter G Lambda)} (R : Output D Delta a word)

theorem other_darts (d : Delta.toCombMap.Dart)
    (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    R.expansion.darts d = [R.expansion.toDartExpansion.first d] := by
  have hlen := congrArg List.length (R.other_word d ha hb)
  simp only [List.length_map, List.length_singleton] at hlen
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hfirst : R.expansion.toDartExpansion.first d = x := by
    simp only [DartExpansion.first, hx, List.head_cons]
  exact hx.trans (congrArg List.singleton hfirst.symm)

theorem other_last (d : Delta.toCombMap.Dart)
    (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    R.expansion.toDartExpansion.last d = R.expansion.toDartExpansion.first d := by
  simp only [DartExpansion.last, R.other_darts d ha hb, List.getLast_singleton]

theorem other_label (d : Delta.toCombMap.Dart)
    (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    R.diagram.label (R.expansion.toDartExpansion.first d) = Delta.label d := by
  have h := R.other_word d ha hb
  rwa [R.other_darts d ha hb, List.map_singleton, List.singleton_inj] at h

theorem other_alpha (d : Delta.toCombMap.Dart)
    (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    R.diagram.toCombMap.alpha (R.expansion.toDartExpansion.first d) =
      R.expansion.toDartExpansion.first (Delta.toCombMap.alpha d) := by
  rw [R.expansion.toDartExpansion.first_alpha, R.other_last d ha hb]

theorem other_facePerm (d : Delta.toCombMap.Dart)
    (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    R.diagram.toCombMap.facePerm (R.expansion.toDartExpansion.first d) =
      R.expansion.toDartExpansion.first (Delta.toCombMap.facePerm d) := by
  have h := R.expansion.join d
  change R.diagram.toCombMap.facePerm (R.expansion.toDartExpansion.last d) = _ at h
  rwa [R.other_last d ha hb] at h

end GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.Output

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.Output.other_darts
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.Output.other_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.Output.other_facePerm
