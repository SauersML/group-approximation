import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# Boundary arcs of the glued pocket diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): a region of a copy of `Γ_1` whose target
arc lies on a boundary arc of `Δ` glues back into a region of a copy of `Δ` whose target arc lies
on the same boundary arc.

Let `P` be a pocket region of `Δ` whose complement cycle follows the boundary, and `Ξ` an
O-equivalent copy of the pocket diagram, glued back along that cycle
(`PocketRegion.glueDiagram`).  The outer face of `Ξ` is glued to the complement cycle position by
position.  When an arc of the outer boundary of `Δ` occurs in the reversed complement cycle, the
outer darts of `Ξ` at those positions go to the outer darts of the glued diagram on that arc.

* `Embedded.CyclicArc.getElem_darts_of_le`: the darts of an arc that does not wrap around.
* `PocketRegion.glueEmbedding_outerBoundary_getElem`: the seam, position by position.
* `PocketRegion.glueDiagram_outerBoundary_getElem`: the outer face of the glued diagram carries
  the outer face of `Δ`.
* `PocketRegion.glueEmbedding_outerDarts_getElem`: an outer dart of `Ξ` on the arc is an outer
  dart of the glued diagram.
* `PocketRegion.exists_glue_outerArc`: an outer arc of `Ξ` on the arc is an outer arc of the glued
  diagram, shifted to the position of the arc.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

/-- The darts of an arc that does not wrap around are the darts of its cycle from its start. -/
theorem Embedded.CyclicArc.getElem_darts_of_le {Dart : Type v} {cycle : List Dart}
    (arc : CyclicArc cycle) (hend : arc.start.1 + arc.length ≤ cycle.length) {k : ℕ}
    (hk : k < arc.darts.length) :
    arc.darts[k] = cycle[arc.start.1 + k]'(by rw [arc.darts_length] at hk; omega) := by
  have hk' : k < arc.length := by rw [arc.darts_length] at hk; exact hk
  have hdrop : k < (cycle.drop arc.start.1).length := by rw [List.length_drop]; omega
  simp only [CyclicArc.darts, CyclicArc.rotated, List.getElem_take]
  rw [List.getElem_append_left hdrop, List.getElem_drop]

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- A dart of the outer face of the copy is glued to the complement-cycle dart at its
position. -/
theorem glueEmbedding_outerBoundary_getElem (O : OEquivalentDiscDiagram P.diagram Xi) {i : ℕ}
    (hi : i < P.outer.cycle.length) (hi' : i < (Xi.faceBoundary Xi.outerFace).darts.length) :
    (P.glueSeam O).glueEmbedding (Xi.faceBoundary Xi.outerFace).darts[i] =
      (P.glueSeam O).faceDart P.outer.cycle[i]
        ((P.outer.cycle_mem_iff _).1 (List.getElem_mem hi)).1 := by
  have h := (P.glueSeam O).glueEmbedding_seam ((P.glueSeam O).boundary.positionEquiv ⟨i, hi⟩)
  rw [Seam.seamEquiv_positionEquiv, Seam.outerPosition_val] at h
  exact h

/-- The outer face of the glued diagram carries the outer face of `Δ`. -/
theorem glueDiagram_outerBoundary_darts (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) :
    ((P.glueDiagram O hwalk).faceBoundary (P.glueDiagram O hwalk).outerFace).darts =
      (P.glueSeam O).leftDarts Delta.outerFace P.outerFace_mem
        (Delta.faceBoundary Delta.outerFace) :=
  (P.glueSeam O).glueFaceBoundary_leftFace_darts Delta.faceBoundary Xi.faceBoundary
    Delta.outerFace P.outerFace_mem

/-- The outer face of the glued diagram carries the outer face of `Δ`, position by position. -/
theorem glueDiagram_outerBoundary_getElem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) {i : ℕ}
    (hi : i <
      ((P.glueDiagram O hwalk).faceBoundary (P.glueDiagram O hwalk).outerFace).darts.length)
    (hi' : i < (Delta.faceBoundary Delta.outerFace).darts.length) :
    ((P.glueDiagram O hwalk).faceBoundary (P.glueDiagram O hwalk).outerFace).darts[i] =
      (P.glueSeam O).faceDart (Delta.faceBoundary Delta.outerFace).darts[i]
        ((P.glueSeam O).faceOf_mem_of_mem_darts Delta.outerFace P.outerFace_mem
          (Delta.faceBoundary Delta.outerFace) _ (List.getElem_mem hi')) :=
  (getElem_congr_coll (P.glueDiagram_outerBoundary_darts O hwalk)).trans
    (List.getElem_pmap _ _ _)

theorem length_glueDiagram_outerBoundary (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) :
    ((P.glueDiagram O hwalk).faceBoundary (P.glueDiagram O hwalk).outerFace).darts.length =
      (Delta.faceBoundary Delta.outerFace).darts.length :=
  (congrArg List.length (P.glueDiagram_outerBoundary_darts O hwalk)).trans List.length_pmap

theorem length_outerDarts_glueDiagram (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) :
    (outerDarts (P.glueDiagram O hwalk)).length = (outerDarts Delta).length := by
  simp only [outerDarts, List.length_map, List.length_reverse]
  exact P.length_glueDiagram_outerBoundary O hwalk

theorem length_outerDarts_copy (O : OEquivalentDiscDiagram P.diagram Xi) :
    (outerDarts Xi).length = P.outer.cycle.length := by
  simp only [outerDarts, List.length_map, List.length_reverse]
  exact (P.glueSeam O).length_eq.symm

/-- **An outer dart of the copy on a boundary arc of `Δ` is an outer dart of the glued
diagram.** -/
theorem glueEmbedding_outerDarts_getElem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (arc : CyclicArc (outerDarts Delta))
    (hend : arc.start.1 + arc.length ≤ (outerDarts Delta).length)
    (pre post : List Delta.toCombMap.Dart)
    (hdec : invDarts Delta P.outer.cycle = pre ++ arc.darts ++ post) {k : ℕ}
    (hpre : pre.length ≤ k) (hk : k < pre.length + arc.length)
    (hkX : k < (outerDarts Xi).length)
    (hkY : arc.start.1 + (k - pre.length) < (outerDarts (P.glueDiagram O hwalk)).length) :
    (P.glueEmbeddingAway O hwalk).darts (outerDarts Xi)[k] =
      (outerDarts (P.glueDiagram O hwalk))[arc.start.1 + (k - pre.length)] := by
  have hL := P.length_outerDarts_copy O
  have hxb : (Xi.faceBoundary Xi.outerFace).darts.length = P.outer.cycle.length := by
    simpa only [outerDarts, List.length_map, List.length_reverse] using hL
  have hob : (outerDarts Delta).length = (Delta.faceBoundary Delta.outerFace).darts.length := by
    simp only [outerDarts, List.length_map, List.length_reverse]
  have hyb := P.length_glueDiagram_outerBoundary O hwalk
  have hlen : k < (pre ++ arc.darts).length := by
    rw [List.length_append, arc.darts_length]; exact hk
  -- the complement-cycle dart at `k` is the outer dart of `Δ` on the arc
  have hinv : (invDarts Delta P.outer.cycle)[k]'(by
      rw [invDarts, List.length_map, List.length_reverse]; omega) =
      (outerDarts Delta)[arc.start.1 + (k - pre.length)]'(by omega) := by
    simp only [hdec]
    rw [List.getElem_append_left hlen, List.getElem_append_right hpre]
    exact arc.getElem_darts_of_le hend (by rw [arc.darts_length]; omega)
  simp only [invDarts, outerDarts, List.getElem_map, List.getElem_reverse] at hinv
  simp only [outerDarts, List.getElem_map, List.getElem_reverse, hxb, hyb]
  rw [← (P.glueEmbeddingAway O hwalk).alpha]
  congr 1
  exact (P.glueEmbedding_outerBoundary_getElem O (by omega) (by omega)).trans
    (((P.glueSeam O).faceDart_congr (Delta.toCombMap.alpha.injective hinv) _ _).trans
      (P.glueDiagram_outerBoundary_getElem O hwalk (by omega) (by omega)).symm)

/-- **An outer arc of the copy on a boundary arc of `Δ` is an outer arc of the glued
diagram.** Positions `pre.length ≤ j < pre.length + arc.length` of the reversed complement cycle
carry the arc, so an arc of the outer boundary of `Ξ` inside these positions is carried to the
arc of the outer boundary of the glued diagram at the same offset from the start of `arc`. -/
theorem exists_glue_outerArc (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (arc : CyclicArc (outerDarts Delta))
    (hend : arc.start.1 + arc.length ≤ (outerDarts Delta).length)
    (pre post : List Delta.toCombMap.Dart)
    (hdec : invDarts Delta P.outer.cycle = pre ++ arc.darts ++ post)
    (A : CyclicArc (outerDarts Xi)) (hpre : pre.length ≤ A.start.1)
    (hA : A.start.1 + A.length ≤ pre.length + arc.length) :
    ∃ B : CyclicArc (outerDarts (P.glueDiagram O hwalk)),
      B.start.1 = arc.start.1 + (A.start.1 - pre.length) ∧ B.length = A.length ∧
        B.darts = A.darts.map (P.glueEmbeddingAway O hwalk).darts := by
  have hL := P.length_outerDarts_copy O
  have hN := P.length_outerDarts_glueDiagram O hwalk
  have hcl : P.outer.cycle.length = pre.length + arc.length + post.length := by
    have h := congrArg List.length hdec
    rw [invDarts, List.length_map, List.length_reverse, List.length_append, List.length_append,
      arc.darts_length] at h
    exact h
  obtain ⟨B, hBs, hBl⟩ : ∃ B : CyclicArc (outerDarts (P.glueDiagram O hwalk)),
      B.start.1 = arc.start.1 + (A.start.1 - pre.length) ∧ B.length = A.length :=
    ⟨⟨⟨arc.start.1 + (A.start.1 - pre.length), by omega⟩, A.length, by omega⟩, rfl, rfl⟩
  refine ⟨B, hBs, hBl, ?_⟩
  apply List.ext_getElem
  · rw [B.darts_length, List.length_map, A.darts_length, hBl]
  · intro m hm1 hm2
    have hm : m < A.length := by rw [List.length_map, A.darts_length] at hm2; exact hm2
    have hmA : m < A.darts.length := by rw [A.darts_length]; exact hm
    rw [B.getElem_darts_of_le (by omega) hm1, List.getElem_map,
      A.getElem_darts_of_le (by omega) hmA,
      P.glueEmbedding_outerDarts_getElem O hwalk arc hend pre post hdec (k := A.start.1 + m)
        (by omega) (by omega) (by omega) (by omega)]
    exact getElem_congr_idx (by omega)

/-- The image arc of `exists_glue_outerArc` lies inside `arc`. -/
theorem exists_glue_outerArc_within (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (arc : CyclicArc (outerDarts Delta))
    (hend : arc.start.1 + arc.length ≤ (outerDarts Delta).length)
    (pre post : List Delta.toCombMap.Dart)
    (hdec : invDarts Delta P.outer.cycle = pre ++ arc.darts ++ post)
    (A : CyclicArc (outerDarts Xi)) (hpre : pre.length ≤ A.start.1)
    (hA : A.start.1 + A.length ≤ pre.length + arc.length) :
    ∃ B : CyclicArc (outerDarts (P.glueDiagram O hwalk)),
      arc.start.1 ≤ B.start.1 ∧ B.start.1 + B.length ≤ arc.start.1 + arc.length ∧
        B.darts = A.darts.map (P.glueEmbeddingAway O hwalk).darts := by
  obtain ⟨B, hBs, hBl, hBd⟩ := P.exists_glue_outerArc O hwalk arc hend pre post hdec A hpre hA
  exact ⟨B, by omega, by omega, hBd⟩

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.getElem_darts_of_le
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueEmbedding_outerBoundary_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueDiagram_outerBoundary_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueEmbedding_outerDarts_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_glue_outerArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_glue_outerArc_within
