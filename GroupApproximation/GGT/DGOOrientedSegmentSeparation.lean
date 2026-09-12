import GroupApproximation.GGT.DGOOrientedComponentCoset

/-!
# A geodesic component does not reconnect to a segment excluding its edge

The opponent may start at a cut, so its maximal component in the whole word
need not begin there. The isolated-singleton letter lemma avoids assuming that
maximality survives the cut and treats both orientations of the segment.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A component edge of a geodesic word has no coset connection to a same-label
letter in an oriented segment which excludes that edge. -/
theorem not_connected_orientedSegment_of_outside_component
    (D : RelGenSet G Lambda) {lam : Lambda} {v endpoint : G}
    {word : List (RelLetter G Lambda)} (hgeo : IsGeodesicWord D v endpoint word)
    {cs cf y r : ℕ} (hcs : cs ≤ word.length) (hcf : cf ≤ word.length)
    (hcomp : IsComp lam word y (y + 1)) (hout : ¬ EdgeBetween cs cf y)
    (hr : r < (orientedSegment word cs cf).length)
    (hletter : ((orientedSegment word cs cf)[r]'hr).IsCompOf lam) :
    ¬ (vertex v word y)⁻¹ * vertex (vertex v word cs) (orientedSegment word cs cf) r ∈ D.fam lam := by
  intro hconn
  have hiso : IsIsolated D.fam lam v word y := by
    refine ⟨⟨y + 1, hcomp⟩, ?_⟩
    intro q hne hq
    exact not_connected_of_isCompStart_of_geodesic D hgeo ⟨y + 1, hcomp⟩ hq hne.symm
  by_cases hor : cs ≤ cf
  · have hwidth : r < cf - cs := by
      rwa [length_orientedSegment word hcs hcf, Nat.dist_eq_sub_of_le hor] at hr
    have hm : cs + r < word.length := by omega
    have hco := (isCompOf_getElem_orientedSegment_of_le lam word hor hr hm).mp hletter
    rw [vertex_orientedSegment_of_le word v hor hwidth.le] at hconn
    have heq := eq_of_isolated_singleton_of_connected_letter D hgeo.1 hcomp hiso
      hm le_rfl (Nat.le_succ _) hco hconn
    apply hout
    unfold EdgeBetween
    omega
  · have hwidth : r < cs - cf := by
      rwa [length_orientedSegment word hcs hcf, Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega)] at hr
    have hm : cs - 1 - r < word.length := by omega
    have hco := (isCompOf_getElem_orientedSegment_of_not_le lam word hor hcs hr hm).mp hletter
    rw [vertex_orientedSegment_of_not_le word v hor hcs hwidth.le] at hconn
    have heq := eq_of_isolated_singleton_of_connected_letter D hgeo.1 hcomp hiso
      hm (z := cs - r) (by omega) (by omega) hco hconn
    apply hout
    unfold EdgeBetween
    omega

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.not_connected_orientedSegment_of_outside_component
