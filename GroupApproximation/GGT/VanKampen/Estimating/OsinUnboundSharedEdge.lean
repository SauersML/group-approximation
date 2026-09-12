import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Unbound darts on an edge shared with another relator cell or the exterior

Osin's Appendix (arXiv:math/0411039v3, §9) passes to 0-refined diagrams, where the
boundary of a relator cell meets only G-cells.  In an arbitrary diagram a dart of a
relator cell can lie on an edge whose other side is another relator cell (possibly the
same one) or the exterior.  If that dart is unbound for a section family of maximal
weight, the family is not maximal: doubling the edge (`FaceEdgeDoubling.diagram`) creates
a G-cell digon between the two sides, which is a contiguity region of arc lengths one and
one with empty sides, and adjoining it to the retained family raises the weight by two
(`RealizedSectionFamily.false_of_unbound_shared_edge`).

Toward the exterior the digon's target arc is one position of the boundary word, which
lies in some section (`SectionCuts.exists_section_of_lt`), so the enlarged family still
respects the sections.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace SectionCuts

/-- Every position of the word lies in some section. -/
theorem exists_section_of_lt {D : RelGenSet G Lambda} {lambda c : ℝ}
    {word : List (RelLetter G Lambda)} (cuts : SectionCuts D lambda c word) {p : ℕ}
    (hp : p < word.length) :
    ∃ j : Fin cuts.count, cuts.cut j.castSucc ≤ p ∧ p + 1 ≤ cuts.cut j.succ := by
  have hex : ∃ m : ℕ, ∃ hm : m < cuts.count + 1, p < cuts.cut ⟨m, hm⟩ :=
    ⟨cuts.count, Nat.lt_succ_self _, by
      have h := cuts.cut_last
      change cuts.cut ⟨cuts.count, Nat.lt_succ_self _⟩ = word.length at h
      rw [h]
      exact hp⟩
  obtain ⟨hm, hpm⟩ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have h := cuts.cut_zero
    have hcut : cuts.cut ⟨Nat.find hex, hm⟩ = cuts.cut 0 := congrArg cuts.cut (Fin.ext h0)
    rw [hcut, h] at hpm
    exact Nat.not_lt_zero _ hpm
  have hlt : Nat.find hex - 1 < cuts.count := by omega
  refine ⟨⟨Nat.find hex - 1, hlt⟩, ?_, ?_⟩
  · by_contra hnot
    push Not at hnot
    exact Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex) ⟨by omega, hnot⟩
  · have hsucc : (⟨Nat.find hex - 1, hlt⟩ : Fin cuts.count).succ = ⟨Nat.find hex, hm⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [hsucc]
    exact hpm

end SectionCuts

namespace FaceEdgeDoubling

/-- The arc of length one at position `p` of a traversal. -/
def unitArc {α : Type*} (cycle : List α) (p : ℕ) (hp : p < cycle.length) : CyclicArc cycle where
  start := ⟨p, by omega⟩
  length := 1
  length_le := by omega

theorem unitArc_darts {α : Type*} (cycle : List α) (p : ℕ) (hp : p < cycle.length) :
    (unitArc cycle p hp).darts = [cycle[p]] := by
  change (cycle.drop p ++ cycle.take p).take 1 = _
  rewrite [List.drop_eq_getElem_cons hp]
  rfl

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- A retained dart other than `w_j` is off the digon. -/
theorem faceOf_embed_ne_digon {x : Delta.toCombMap.Dart} (hx : x ≠ dart Delta f j) :
    (diagram Delta f j hlen hf).toCombMap.faceOf (EdgeInsertion.embed Delta.toCombMap x) ≠
      digon Delta f j hlen := by
  by_cases hxf : Delta.toCombMap.faceOf x = f
  · have hmem : EdgeInsertion.embed Delta.toCombMap x ∈
        (boundary Delta f j hlen (cellFace Delta f j hlen)).darts := by
      rw [boundary_cellFace_darts]
      refine List.mem_map.mpr ⟨x, ((Delta.faceBoundary f).mem_iff x).mpr hxf, ?_⟩
      rw [dartImage, if_neg hx]
    have hface := ((boundary Delta f j hlen (cellFace Delta f j hlen)).mem_iff _).mp hmem
    change (map Delta f j hlen).faceOf (EdgeInsertion.embed Delta.toCombMap x) ≠ _
    rw [hface]
    exact (digon_ne_cellFace Delta f j hlen).symm
  · have hface := EdgeInsertion.faceOf_embed_eq_keptFace Delta.toCombMap _ _
      (EdgeInsertion.corners_face_eq Delta.toCombMap (rebased Delta f j) (second Delta f j hlen))
      (Delta.toCombMap.faceOf x)
      (by rwa [EdgeInsertion.firstCorner_face Delta.toCombMap (rebased Delta f j)]) x rfl
    change (map Delta f j hlen).faceOf (EdgeInsertion.embed Delta.toCombMap x) ≠ _
    rw [hface]
    exact keep_ne_digon Delta f j hlen hxf

/-- The digon has no internally paired dart. -/
theorem digon_noInternalFaceDart :
    Surgery.MapCollapse.NoInternalFaceDart (diagram Delta f j hlen hf).toCombMap
      (digon Delta f j hlen) := by
  intro x hx halpha
  have hmem : x ∈ (boundary Delta f j hlen (digon Delta f j hlen)).darts :=
    ((boundary Delta f j hlen (digon Delta f j hlen)).mem_iff x).mpr hx
  rw [boundary_digon] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact digon_ne_cellFace Delta f j hlen halpha.symm
  · have hx' : x = EdgeInsertion.embed Delta.toCombMap (dart Delta f j) :=
      List.mem_singleton.mp hmem'
    subst hx'
    exact faceOf_embed_ne_digon Delta f j hlen hf
      (Delta.toCombMap.alpha_fixedPointFree (dart Delta f j)) halpha

theorem digon_ne_outer : digon Delta f j hlen ≠ (diagram Delta f j hlen hf).outerFace :=
  (keep_ne_digon Delta f j hlen hf.symm).symm

theorem digon_value :
    RelLetter.listVal ((diagram Delta f j hlen hf).faceWord (digon Delta f j hlen)) = 1 :=
  boundary_digon_value Delta f j hlen

/-- The new dart in the place of `w_j`, read backwards, is the other new dart. -/
theorem invDarts_carrierImage_self_dart :
    invDarts (diagram Delta f j hlen hf) [carrierImage Delta f j hlen hf f (dart Delta f j)] =
      [none] := by
  rewrite [carrierImage_self, dartImage, if_pos rfl]
  rfl

/-- A retained dart, read backwards, is the retained reverse dart. -/
theorem invDarts_embedding_alpha (x : Delta.toCombMap.Dart) :
    invDarts (diagram Delta f j hlen hf)
        [(embedding Delta f j hlen hf).darts (Delta.toCombMap.alpha x)] =
      [EdgeInsertion.embed Delta.toCombMap x] := by
  rewrite [invDarts, List.reverse_singleton, List.map_singleton,
    (embedding Delta f j hlen hf).alpha, Delta.toCombMap.alpha_involutive x]
  rfl

end FaceEdgeDoubling

namespace RealizedSectionFamily

open FaceEdgeDoubling

/-- **An unbound dart on an edge shared with a relator cell or the exterior contradicts
maximality.** -/
theorem false_of_unbound_shared_edge {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
      other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
        other.weight ≤ S.weight)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart)
    (hd : d ∈ RegionCandidate.unboundDarts S.family i)
    (hlen : 1 < (cellDarts S.diagram i).length)
    (hadj : (∃ i₂ : Fin S.diagram.rCellCount,
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = (cell S.diagram i₂).face) ∨
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = S.diagram.outerFace) :
    False := by
  have hf : (cell S.diagram i).face ≠ S.diagram.outerFace := (cell S.diagram i).face_ne_outer
  have hdmem : d ∈ cellDarts S.diagram i := List.mem_toFinset.mp (Finset.mem_sdiff.mp hd).1
  obtain ⟨j, hj⟩ := List.get_of_mem hdmem
  have hdart : dart S.diagram (cell S.diagram i).face j = d := by
    rw [dart_eq_get]
    exact hj
  /- The regions avoid every relator face and the exterior. -/
  have hnotRelator : ∀ a ∈ S.family, ∀ C ∈ S.diagram.relatorCells, C.face ∉ a.1 := by
    intro a _ C hC hmem
    have h := (a.2.boundary.all_gCells C.face hmem).2
    rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word C hC] at h
    exact hvalue C hC h
  have havoid : ∀ a ∈ S.family, (cell S.diagram i).face ∉ a.1 ∧
      S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha (dart S.diagram (cell S.diagram i).face j)) ∉ a.1 := by
    intro a ha
    refine ⟨hnotRelator a ha _ (cell_mem S.diagram i), ?_⟩
    rw [hdart]
    rcases hadj with ⟨i₂, hi₂⟩ | hout
    · rw [hi₂]
      exact hnotRelator a ha _ (cell_mem S.diagram i₂)
    · rw [hout]
      intro hmem
      exact (a.2.boundary.all_gCells _ hmem).1 rfl
  let Xi := diagram S.diagram (cell S.diagram i).face j hlen hf
  let C := cellMap S.diagram (cell S.diagram i).face j hlen hf
  let family1 := regionFamily S.diagram (cell S.diagram i).face j hlen hf S.family havoid
  /- The source arc: the new dart, at position `j` of the carrier of cell `i`. -/
  let sourceArc : CyclicArc (cellDarts Xi (C.indexEquiv i)) :=
    (unitArc (cellDarts S.diagram i) j.val j.isLt).mapTo
      (carrierImage S.diagram (cell S.diagram i).face j hlen hf (cell S.diagram i).face)
      (cellDarts_eq S.diagram (cell S.diagram i).face j hlen hf i)
  have hsourceRev : sourceArc.reverseDarts = [none] := by
    change invDarts Xi ((unitArc (cellDarts S.diagram i) j.val j.isLt).mapTo
      (carrierImage S.diagram (cell S.diagram i).face j hlen hf (cell S.diagram i).face)
      (cellDarts_eq S.diagram (cell S.diagram i).face j hlen hf i)).darts = _
    have h1 : (cellDarts S.diagram i)[j.val]'j.isLt = dart S.diagram (cell S.diagram i).face j :=
      (dart_eq_get S.diagram (cell S.diagram i).face j).symm
    rewrite [CyclicArc.mapTo_darts, unitArc_darts, h1, List.map_singleton]
    exact invDarts_carrierImage_self_dart S.diagram (cell S.diagram i).face j hlen hf
  /- The target side and the digon region. -/
  have hdigonWord : (Xi.faceBoundary (digon S.diagram (cell S.diagram i).face j hlen)).darts =
      [none, EdgeInsertion.embed S.diagram.toCombMap d] := by
    rewrite [← hdart]
    exact boundary_digon S.diagram (cell S.diagram i).face j hlen
  obtain ⟨t, targetArc, hdecomp, htlen, hrespectsDigon⟩ :
      ∃ (t : Option (Fin Xi.rCellCount)) (targetArc : CyclicArc (targetDarts Xi t)),
        (Xi.faceBoundary (digon S.diagram (cell S.diagram i).face j hlen)).darts.rotate 0 =
          sourceArc.reverseDarts ++ [] ++ targetBoundaryDarts Xi t targetArc ++ [] ∧
        targetArc.length = 1 ∧
        (t = none → ∃ jc : Fin cuts.count, cuts.cut jc.castSucc ≤ targetArc.start.val ∧
          targetArc.start.val + targetArc.length ≤ cuts.cut jc.succ) := by
    rcases hadj with ⟨i₂, hi₂⟩ | hout
    · have hmem2 : S.diagram.toCombMap.alpha d ∈ cellDarts S.diagram i₂ :=
        ((S.diagram.faceBoundary (cell S.diagram i₂).face).mem_iff _).mpr hi₂
      obtain ⟨q, hq⟩ := List.get_of_mem hmem2
      refine ⟨some (C.indexEquiv i₂),
        (unitArc (cellDarts S.diagram i₂) q.val q.isLt).mapTo
          (carrierImage S.diagram (cell S.diagram i).face j hlen hf (cell S.diagram i₂).face)
          (cellDarts_eq S.diagram (cell S.diagram i).face j hlen hf i₂),
        ?_, CyclicArc.mapTo_length _ _ _, fun h => by cases h⟩
      rewrite [List.rotate_zero, hdigonWord, hsourceRev]
      change [none, EdgeInsertion.embed S.diagram.toCombMap d] =
        [none] ++ [] ++ invDarts (diagram S.diagram (cell S.diagram i).face j hlen hf)
          ((unitArc (cellDarts S.diagram i₂) q.val q.isLt).mapTo
          (carrierImage S.diagram (cell S.diagram i).face j hlen hf (cell S.diagram i₂).face)
          (cellDarts_eq S.diagram (cell S.diagram i).face j hlen hf i₂)).darts ++ []
      have h2 : (cellDarts S.diagram i₂)[q.val]'q.isLt = S.diagram.toCombMap.alpha d := hq
      have hne : S.diagram.toCombMap.alpha d ≠ dart S.diagram (cell S.diagram i).face j := by
        rw [hdart]
        exact S.diagram.toCombMap.alpha_fixedPointFree d
      rewrite [CyclicArc.mapTo_darts, unitArc_darts, h2, List.map_singleton,
        carrierImage_of_ne_dart S.diagram (cell S.diagram i).face j hlen hf
          (cell S.diagram i₂).face hne,
        invDarts_embedding_alpha S.diagram (cell S.diagram i).face j hlen hf d]
      rfl
    · have hmem2 : d ∈ outerDarts S.diagram := by
        refine List.mem_map.mpr ⟨S.diagram.toCombMap.alpha d, List.mem_reverse.mpr ?_, ?_⟩
        · exact ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff _).mpr hout
        · exact S.diagram.toCombMap.alpha_involutive d
      obtain ⟨p, hp⟩ := List.get_of_mem hmem2
      refine ⟨none, (unitArc (outerDarts S.diagram) p.val p.isLt).mapTo
          (targetImage S.diagram (cell S.diagram i).face j hlen hf none)
          (targetDarts_eq S.diagram (cell S.diagram i).face j hlen hf none),
        ?_, CyclicArc.mapTo_length _ _ _, ?_⟩
      · rewrite [List.rotate_zero, hdigonWord, hsourceRev]
        change [none, EdgeInsertion.embed S.diagram.toCombMap d] =
          [none] ++ [] ++ ((unitArc (outerDarts S.diagram) p.val p.isLt).mapTo
            (targetImage S.diagram (cell S.diagram i).face j hlen hf none)
            (targetDarts_eq S.diagram (cell S.diagram i).face j hlen hf none)).darts ++ []
        have h2 : (outerDarts S.diagram)[p.val]'p.isLt = d := hp
        rewrite [CyclicArc.mapTo_darts, unitArc_darts, h2, List.map_singleton]
        rfl
      · intro _
        have hlenOuter : p.val < Delta.boundaryWord.length := by
          have h1 := p.isLt
          have h2 : (outerDarts S.diagram).length = S.diagram.boundaryWord.length := by
            simp only [outerDarts, DiscDiagram.boundaryWord, HullSC.RelWord.revInv,
              DiscDiagram.faceWord, List.length_map, List.length_reverse]
          rw [S.equiv.boundaryWord_eq] at h2
          omega
        obtain ⟨jc, h1, h2⟩ := cuts.exists_section_of_lt hlenOuter
        refine ⟨jc, ?_, ?_⟩
        · rw [CyclicArc.mapTo_start]
          exact h1
        · rw [CyclicArc.mapTo_start, CyclicArc.mapTo_length]
          exact h2
  let H : ContiguityGeometry D eps Xi {digon S.diagram (cell S.diagram i).face j hlen} :=
    ContiguityGeometry.ofSingletonFace (digon S.diagram (cell S.diagram i).face j hlen)
      (digon_ne_outer S.diagram (cell S.diagram i).face j hlen hf)
      (digon_value S.diagram (cell S.diagram i).face j hlen hf)
      (digon_noInternalFaceDart S.diagram (cell S.diagram i).face j hlen hf) 0
      (C.indexEquiv i) t sourceArc targetArc [] [] hdecomp (Nat.zero_le _) (Nat.zero_le _)
      (by simp only [dartWord, List.map_nil, RelLetter.listVal_nil, WordMetric.wordNorm_one,
        Nat.zero_le])
      (by simp only [dartWord, List.map_nil, RelLetter.listVal_nil, WordMetric.wordNorm_one,
        Nat.zero_le])
  have havoid1 : ∀ a ∈ family1, digon S.diagram (cell S.diagram i).face j hlen ∉ a.1 := by
    intro a ha hmem
    obtain ⟨b, hb, hab⟩ :=
      regionFamily_faces S.diagram (cell S.diagram i).face j hlen hf S.family havoid ha
    rw [hab] at hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact keep_ne_digon S.diagram (cell S.diagram i).face j hlen
      (fun h => (havoid b hb).1 (h ▸ hg)) hgeq
  have hsourceLen : H.sourceArc.length = 1 := CyclicArc.mapTo_length _ _ _
  have hlt := RegionCandidate.familyWeight_lt_cons_singleton H havoid1
    (by rw [hsourceLen]; exact Nat.one_pos)
  have hrespects : ∀ a ∈ Finset.cons
      (⟨{digon S.diagram (cell S.diagram i).face j hlen}, H⟩ : RegionCandidate D eps Xi)
      family1 (RegionCandidate.singleton_not_mem_of_avoid H havoid1),
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha1
    · intro hnone
      obtain ⟨jc, h1, h2⟩ := hrespectsDigon hnone
      exact ⟨jc, hnone, h1, h2⟩
    · obtain ⟨b, hb, hab⟩ :=
        regionFamily_profile S.diagram (cell S.diagram i).face j hlen hf S.family havoid ha1
      exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  have hnondegenerate : ∀ a ∈ Finset.cons
      (⟨{digon S.diagram (cell S.diagram i).face j hlen}, H⟩ : RegionCandidate D eps Xi)
      family1 (RegionCandidate.singleton_not_mem_of_avoid H havoid1),
      0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha1
    · refine ⟨by rw [hsourceLen]; exact Nat.one_pos, ?_⟩
      change 0 < targetArc.length
      rw [htlen]
      exact Nat.one_pos
    · obtain ⟨b, hb, hab⟩ :=
        regionFamily_profile S.diagram (cell S.diagram i).face j hlen hf S.family havoid ha1
      obtain ⟨hs, ht⟩ := S.nondegenerate b hb
      exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  have hle : EstimatingSelection.familyWeight RegionCandidate.weight
      (Finset.cons
        (⟨{digon S.diagram (cell S.diagram i).face j hlen}, H⟩ : RegionCandidate D eps Xi)
        family1 (RegionCandidate.singleton_not_mem_of_avoid H havoid1)) ≤
      EstimatingSelection.familyWeight RegionCandidate.weight S.family :=
    hmax
      { diagram := Xi
        equiv := S.equiv.trans (oEquivalent S.diagram (cell S.diagram i).face j hlen hf)
        reduced := reduced S.diagram (cell S.diagram i).face j hlen hf S.reduced
        family := Finset.cons
          (⟨{digon S.diagram (cell S.diagram i).face j hlen}, H⟩ : RegionCandidate D eps Xi)
          family1 (RegionCandidate.singleton_not_mem_of_avoid H havoid1)
        pairwise := RegionCandidate.cons_singleton_pairwise H havoid1
          (regionFamily_pairwise S.diagram (cell S.diagram i).face j hlen hf S.family havoid
            S.pairwise)
        respects := hrespects
        nondegenerate := hnondegenerate }
      (label_admissible S.diagram (cell S.diagram i).face j hlen hf (symmetricLabelAlphabet D)
        (symmetricLabelAlphabet.symmetric D) hlegal)
  have heq : EstimatingSelection.familyWeight RegionCandidate.weight family1 =
      EstimatingSelection.familyWeight RegionCandidate.weight S.family :=
    regionFamily_weight S.diagram (cell S.diagram i).face j hlen hf S.family havoid
  exact absurd hle (not_le.mpr (lt_of_eq_of_lt heq.symm hlt))

end RealizedSectionFamily
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.exists_section_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.digon_noInternalFaceDart
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_unbound_shared_edge
