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
one with empty sides (`FaceEdgeDoubling.digon_decomposition`), and adjoining it to the
retained family raises the weight by two (`RealizedSectionFamily.false_of_digon_region`,
`RealizedSectionFamily.false_of_unbound_shared_edge`).

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

namespace Embedded

/-- An empty side reads the identity, of word norm zero. -/
theorem wordNorm_dartWord_nil_le (D : RelGenSet G Lambda) (eps : ℕ)
    (Xi : DiscDiagram.{u, w, v} W) :
    WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Xi [])) ≤ eps := by
  rw [dartWord, List.map_nil, RelLetter.listVal_nil, WordMetric.wordNorm_one]
  exact Nat.zero_le _

end Embedded

namespace FaceEdgeDoubling

/-! ## The digon at an edge of relator cell `i` as a contiguity region -/

variable (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount)
  (j : Fin (cellDarts Delta i).length) (hlen : 1 < (cellDarts Delta i).length)
  (hf : (Embedded.cell Delta i).face ≠ Delta.outerFace)

/-- The source arc of the digon: the new dart in the place of `w_j`, at position `j` of the
carrier of cell `i`. -/
noncomputable def sourceUnitArc :
    CyclicArc (cellDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf)
      ((cellMap Delta (Embedded.cell Delta i).face j hlen hf).indexEquiv i)) :=
  (unitArc (cellDarts Delta i) j.val j.isLt).mapTo
    (carrierImage Delta (Embedded.cell Delta i).face j hlen hf (Embedded.cell Delta i).face)
    (cellDarts_eq Delta (Embedded.cell Delta i).face j hlen hf i)

theorem sourceUnitArc_length : (sourceUnitArc Delta i j hlen hf).length = 1 :=
  CyclicArc.mapTo_length (unitArc (cellDarts Delta i) j.val j.isLt)
    (carrierImage Delta (Embedded.cell Delta i).face j hlen hf (Embedded.cell Delta i).face)
    (cellDarts_eq Delta (Embedded.cell Delta i).face j hlen hf i)

/-- The source arc, read backwards, is the other new dart. -/
theorem sourceUnitArc_reverseDarts :
    (sourceUnitArc Delta i j hlen hf).reverseDarts = [none] := by
  have h1 : (cellDarts Delta i)[j.val]'j.isLt = dart Delta (Embedded.cell Delta i).face j :=
    (dart_eq_get Delta (Embedded.cell Delta i).face j).symm
  have h2 : (sourceUnitArc Delta i j hlen hf).darts =
      [carrierImage Delta (Embedded.cell Delta i).face j hlen hf (Embedded.cell Delta i).face
        (dart Delta (Embedded.cell Delta i).face j)] := by
    rw [sourceUnitArc, CyclicArc.mapTo_darts, unitArc_darts, h1, List.map_singleton]
  exact (congrArg (invDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf)) h2).trans
    (invDarts_carrierImage_self_dart Delta (Embedded.cell Delta i).face j hlen hf)

/-- A unit arc of the carrier of cell `i₂`, carried to the doubled diagram. -/
noncomputable def cellUnitArc (i₂ : Fin Delta.rCellCount) (q : ℕ)
    (hq : q < (cellDarts Delta i₂).length) :
    CyclicArc (cellDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf)
      ((cellMap Delta (Embedded.cell Delta i).face j hlen hf).indexEquiv i₂)) :=
  (unitArc (cellDarts Delta i₂) q hq).mapTo
    (carrierImage Delta (Embedded.cell Delta i).face j hlen hf (Embedded.cell Delta i₂).face)
    (cellDarts_eq Delta (Embedded.cell Delta i).face j hlen hf i₂)

theorem cellUnitArc_length (i₂ : Fin Delta.rCellCount) (q : ℕ)
    (hq : q < (cellDarts Delta i₂).length) :
    (cellUnitArc Delta i j hlen hf i₂ q hq).length = 1 :=
  CyclicArc.mapTo_length (unitArc (cellDarts Delta i₂) q hq)
    (carrierImage Delta (Embedded.cell Delta i).face j hlen hf (Embedded.cell Delta i₂).face)
    (cellDarts_eq Delta (Embedded.cell Delta i).face j hlen hf i₂)

/-- At the position of `α w_j` on cell `i₂`, the unit arc as it occurs on a region boundary
is the retained dart `w_j`. -/
theorem cellUnitArc_boundaryDarts (i₂ : Fin Delta.rCellCount) (q : ℕ)
    (hq : q < (cellDarts Delta i₂).length)
    (hget : (cellDarts Delta i₂)[q]'hq =
      Delta.toCombMap.alpha (dart Delta (Embedded.cell Delta i).face j)) :
    targetBoundaryDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf)
        (some ((cellMap Delta (Embedded.cell Delta i).face j hlen hf).indexEquiv i₂))
        (cellUnitArc Delta i j hlen hf i₂ q hq) =
      [EdgeInsertion.embed Delta.toCombMap (dart Delta (Embedded.cell Delta i).face j)] := by
  have hne : Delta.toCombMap.alpha (dart Delta (Embedded.cell Delta i).face j) ≠
      dart Delta (Embedded.cell Delta i).face j :=
    Delta.toCombMap.alpha_fixedPointFree _
  have h3 : (cellUnitArc Delta i j hlen hf i₂ q hq).darts =
      [(embedding Delta (Embedded.cell Delta i).face j hlen hf).darts
        (Delta.toCombMap.alpha (dart Delta (Embedded.cell Delta i).face j))] := by
    rw [cellUnitArc, CyclicArc.mapTo_darts, unitArc_darts, hget, List.map_singleton,
      carrierImage_of_ne_dart Delta (Embedded.cell Delta i).face j hlen hf
        (Embedded.cell Delta i₂).face hne]
  exact (congrArg (invDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf)) h3).trans
    (invDarts_embedding_alpha Delta (Embedded.cell Delta i).face j hlen hf _)

/-- A unit arc of the outer boundary, carried to the doubled diagram. -/
noncomputable def outerUnitArc (p : ℕ) (hp : p < (outerDarts Delta).length) :
    CyclicArc (targetDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf) none) :=
  (unitArc (outerDarts Delta) p hp).mapTo
    (targetImage Delta (Embedded.cell Delta i).face j hlen hf none)
    (targetDarts_eq Delta (Embedded.cell Delta i).face j hlen hf none)

theorem outerUnitArc_length (p : ℕ) (hp : p < (outerDarts Delta).length) :
    (outerUnitArc Delta i j hlen hf p hp).length = 1 :=
  CyclicArc.mapTo_length (unitArc (outerDarts Delta) p hp)
    (targetImage Delta (Embedded.cell Delta i).face j hlen hf none)
    (targetDarts_eq Delta (Embedded.cell Delta i).face j hlen hf none)

theorem outerUnitArc_start (p : ℕ) (hp : p < (outerDarts Delta).length) :
    (outerUnitArc Delta i j hlen hf p hp).start.val = p :=
  CyclicArc.mapTo_start (unitArc (outerDarts Delta) p hp)
    (targetImage Delta (Embedded.cell Delta i).face j hlen hf none)
    (targetDarts_eq Delta (Embedded.cell Delta i).face j hlen hf none)

/-- At the position of `w_j` on the outer boundary, the unit arc is the retained dart `w_j`. -/
theorem outerUnitArc_boundaryDarts (p : ℕ) (hp : p < (outerDarts Delta).length)
    (hget : (outerDarts Delta)[p]'hp = dart Delta (Embedded.cell Delta i).face j) :
    targetBoundaryDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf) none
        (outerUnitArc Delta i j hlen hf p hp) =
      [EdgeInsertion.embed Delta.toCombMap (dart Delta (Embedded.cell Delta i).face j)] := by
  have h3 : (outerUnitArc Delta i j hlen hf p hp).darts =
      [targetImage Delta (Embedded.cell Delta i).face j hlen hf none
        (dart Delta (Embedded.cell Delta i).face j)] := by
    rw [outerUnitArc, CyclicArc.mapTo_darts, unitArc_darts, hget, List.map_singleton]
  exact h3

/-- **The digon as a contiguity region.**  From base zero its boundary is the reversed source
arc, an empty side, a target arc reading the retained dart `w_j`, and an empty side. -/
theorem digon_decomposition
    (t : Option (Fin (diagram Delta (Embedded.cell Delta i).face j hlen hf).rCellCount))
    (targetArc : CyclicArc (targetDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf) t))
    (htarget : targetBoundaryDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf) t
      targetArc =
        [EdgeInsertion.embed Delta.toCombMap (dart Delta (Embedded.cell Delta i).face j)]) :
    ((diagram Delta (Embedded.cell Delta i).face j hlen hf).faceBoundary
        (digon Delta (Embedded.cell Delta i).face j hlen)).darts.rotate 0 =
      (sourceUnitArc Delta i j hlen hf).reverseDarts ++ [] ++
        targetBoundaryDarts (diagram Delta (Embedded.cell Delta i).face j hlen hf) t targetArc ++
          [] := by
  have hdigon : ((diagram Delta (Embedded.cell Delta i).face j hlen hf).faceBoundary
      (digon Delta (Embedded.cell Delta i).face j hlen)).darts =
        [none, EdgeInsertion.embed Delta.toCombMap (dart Delta (Embedded.cell Delta i).face j)] :=
    boundary_digon Delta (Embedded.cell Delta i).face j hlen
  rewrite [List.rotate_zero, hdigon, sourceUnitArc_reverseDarts Delta i j hlen hf, htarget]
  rfl

end FaceEdgeDoubling

namespace RealizedSectionFamily

/-- No selected region contains a relator face whose word does not have value one. -/
theorem faces_not_mem_of_value {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∀ a ∈ S.family, ∀ C ∈ S.diagram.relatorCells, C.face ∉ a.1 := by
  intro a _ C hC hmem
  have h := (a.2.boundary.all_gCells C.face hmem).2
  rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word C hC] at h
  exact hvalue C hC h

/-- **Adjoining a digon region contradicts maximality.**  Double the edge at position `j` of a
face `f` of the diagram of a maximal legal section family, where neither side of the edge lies
in a selected region.  A contiguity region on the digon with nonempty arcs, respecting the
sections, adjoined to the transported family, gives a legal section family of larger weight. -/
theorem false_of_digon_region {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
      other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
        other.weight ≤ S.weight)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧
      S.diagram.toCombMap.faceOf
        (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1)
    (H : ContiguityGeometry D eps (FaceEdgeDoubling.diagram S.diagram f j hlen hf)
      ({FaceEdgeDoubling.digon S.diagram f j hlen} :
        Finset (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.Face))
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length)
    (hsection : H.target = none → ∃ jc : Fin cuts.count,
      cuts.cut jc.castSucc ≤ H.targetArc.start.val ∧
        H.targetArc.start.val + H.targetArc.length ≤ cuts.cut jc.succ) :
    False := by
  have havoid1 : ∀ a ∈ FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid,
      FaceEdgeDoubling.digon S.diagram f j hlen ∉ a.1 := by
    intro a ha hmem
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamily_faces S.diagram f j hlen hf S.family havoid ha
    rw [hab] at hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    refine FaceEdgeDoubling.keep_ne_digon S.diagram f j hlen (g := g) ?_ hgeq
    intro h
    rw [h] at hg
    exact (havoid b hb).1 hg
  have hlt := RegionCandidate.familyWeight_lt_cons_singleton H havoid1 hsource
  have hrespects : ∀ a ∈ Finset.cons
      (⟨{FaceEdgeDoubling.digon S.diagram f j hlen}, H⟩ :
        RegionCandidate D eps (FaceEdgeDoubling.diagram S.diagram f j hlen hf))
      (FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid)
      (RegionCandidate.singleton_not_mem_of_avoid H havoid1),
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha1
    · intro hnone
      obtain ⟨jc, h1, h2⟩ := hsection hnone
      exact ⟨jc, hnone, h1, h2⟩
    · obtain ⟨b, hb, hab⟩ :=
        FaceEdgeDoubling.regionFamily_profile S.diagram f j hlen hf S.family havoid ha1
      exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  have hnondegenerate : ∀ a ∈ Finset.cons
      (⟨{FaceEdgeDoubling.digon S.diagram f j hlen}, H⟩ :
        RegionCandidate D eps (FaceEdgeDoubling.diagram S.diagram f j hlen hf))
      (FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid)
      (RegionCandidate.singleton_not_mem_of_avoid H havoid1),
      0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha1
    · exact ⟨hsource, htarget⟩
    · obtain ⟨b, hb, hab⟩ :=
        FaceEdgeDoubling.regionFamily_profile S.diagram f j hlen hf S.family havoid ha1
      obtain ⟨hs, ht⟩ := S.nondegenerate b hb
      exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  have hle := hmax
    { diagram := FaceEdgeDoubling.diagram S.diagram f j hlen hf
      equiv := S.equiv.trans (FaceEdgeDoubling.oEquivalent S.diagram f j hlen hf)
      reduced := FaceEdgeDoubling.reduced S.diagram f j hlen hf S.reduced
      family := Finset.cons
        (⟨{FaceEdgeDoubling.digon S.diagram f j hlen}, H⟩ :
          RegionCandidate D eps (FaceEdgeDoubling.diagram S.diagram f j hlen hf))
        (FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid)
        (RegionCandidate.singleton_not_mem_of_avoid H havoid1)
      pairwise := RegionCandidate.cons_singleton_pairwise H havoid1
        (FaceEdgeDoubling.regionFamily_pairwise S.diagram f j hlen hf S.family havoid
          S.pairwise)
      respects := hrespects
      nondegenerate := hnondegenerate }
    (FaceEdgeDoubling.label_admissible S.diagram f j hlen hf (symmetricLabelAlphabet D)
      (symmetricLabelAlphabet.symmetric D) hlegal)
  have heq := FaceEdgeDoubling.regionFamily_weight S.diagram f j hlen hf S.family havoid
  exact absurd hle (not_le.mpr (lt_of_eq_of_lt heq.symm hlt))

/-- **Toward a relator cell.**  An edge of cell `i` at position `j` whose other side is
position `q` of cell `i₂`, with both sides off every selected region, contradicts maximality. -/
theorem false_of_digon_toward_cell {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
      other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
        other.weight ≤ S.weight)
    (i : Fin S.diagram.rCellCount) (j : Fin (cellDarts S.diagram i).length)
    (hlen : 1 < (cellDarts S.diagram i).length)
    (havoid : ∀ a ∈ S.family, (cell S.diagram i).face ∉ a.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j)) ∉ a.1)
    (i₂ : Fin S.diagram.rCellCount) (q : ℕ) (hq : q < (cellDarts S.diagram i₂).length)
    (hget : (cellDarts S.diagram i₂)[q]'hq =
      S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j)) :
    False := by
  have hf : (cell S.diagram i).face ≠ S.diagram.outerFace := (cell S.diagram i).face_ne_outer
  refine false_of_digon_region S hlegal hmax (cell S.diagram i).face j hlen hf havoid
    (ContiguityGeometry.ofSingletonFace
      (Delta := FaceEdgeDoubling.diagram S.diagram (cell S.diagram i).face j hlen hf)
      (FaceEdgeDoubling.digon S.diagram (cell S.diagram i).face j hlen)
      (FaceEdgeDoubling.digon_ne_outer S.diagram (cell S.diagram i).face j hlen hf)
      (FaceEdgeDoubling.digon_value S.diagram (cell S.diagram i).face j hlen hf)
      (FaceEdgeDoubling.digon_noInternalFaceDart S.diagram (cell S.diagram i).face j hlen hf) 0
      ((FaceEdgeDoubling.cellMap S.diagram (cell S.diagram i).face j hlen hf).indexEquiv i)
      (some ((FaceEdgeDoubling.cellMap S.diagram (cell S.diagram i).face j hlen hf).indexEquiv
        i₂))
      (FaceEdgeDoubling.sourceUnitArc S.diagram i j hlen hf)
      (FaceEdgeDoubling.cellUnitArc S.diagram i j hlen hf i₂ q hq) [] []
      (FaceEdgeDoubling.digon_decomposition S.diagram i j hlen hf _ _
        (FaceEdgeDoubling.cellUnitArc_boundaryDarts S.diagram i j hlen hf i₂ q hq hget))
      (Nat.zero_le _) (Nat.zero_le _)
      (Embedded.wordNorm_dartWord_nil_le D eps _) (Embedded.wordNorm_dartWord_nil_le D eps _))
    ?_ ?_ ?_
  · exact lt_of_lt_of_eq Nat.one_pos
      (FaceEdgeDoubling.sourceUnitArc_length S.diagram i j hlen hf).symm
  · exact lt_of_lt_of_eq Nat.one_pos
      (FaceEdgeDoubling.cellUnitArc_length S.diagram i j hlen hf i₂ q hq).symm
  · intro h
    exact absurd h (Option.some_ne_none _)

/-- **Toward the exterior.**  An edge of cell `i` at position `j` whose other side is the
exterior, at position `p` of the oriented outer boundary, with the cell off every selected
region, contradicts maximality. -/
theorem false_of_digon_toward_outer {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
      other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
        other.weight ≤ S.weight)
    (i : Fin S.diagram.rCellCount) (j : Fin (cellDarts S.diagram i).length)
    (hlen : 1 < (cellDarts S.diagram i).length)
    (havoid : ∀ a ∈ S.family, (cell S.diagram i).face ∉ a.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j)) ∉ a.1)
    (p : ℕ) (hp : p < (outerDarts S.diagram).length)
    (hget : (outerDarts S.diagram)[p]'hp =
      FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j) :
    False := by
  have hf : (cell S.diagram i).face ≠ S.diagram.outerFace := (cell S.diagram i).face_ne_outer
  have hword : p < Delta.boundaryWord.length := by
    rw [← S.equiv.boundaryWord_eq, ← dartWord_outerDarts S.diagram, dartWord, List.length_map]
    exact hp
  obtain ⟨jc, h1, h2⟩ := cuts.exists_section_of_lt hword
  refine false_of_digon_region S hlegal hmax (cell S.diagram i).face j hlen hf havoid
    (ContiguityGeometry.ofSingletonFace
      (Delta := FaceEdgeDoubling.diagram S.diagram (cell S.diagram i).face j hlen hf)
      (FaceEdgeDoubling.digon S.diagram (cell S.diagram i).face j hlen)
      (FaceEdgeDoubling.digon_ne_outer S.diagram (cell S.diagram i).face j hlen hf)
      (FaceEdgeDoubling.digon_value S.diagram (cell S.diagram i).face j hlen hf)
      (FaceEdgeDoubling.digon_noInternalFaceDart S.diagram (cell S.diagram i).face j hlen hf) 0
      ((FaceEdgeDoubling.cellMap S.diagram (cell S.diagram i).face j hlen hf).indexEquiv i) none
      (FaceEdgeDoubling.sourceUnitArc S.diagram i j hlen hf)
      (FaceEdgeDoubling.outerUnitArc S.diagram i j hlen hf p hp) [] []
      (FaceEdgeDoubling.digon_decomposition S.diagram i j hlen hf _ _
        (FaceEdgeDoubling.outerUnitArc_boundaryDarts S.diagram i j hlen hf p hp hget))
      (Nat.zero_le _) (Nat.zero_le _)
      (Embedded.wordNorm_dartWord_nil_le D eps _) (Embedded.wordNorm_dartWord_nil_le D eps _))
    ?_ ?_ ?_
  · exact lt_of_lt_of_eq Nat.one_pos
      (FaceEdgeDoubling.sourceUnitArc_length S.diagram i j hlen hf).symm
  · exact lt_of_lt_of_eq Nat.one_pos
      (FaceEdgeDoubling.outerUnitArc_length S.diagram i j hlen hf p hp).symm
  · intro _
    have h3 := FaceEdgeDoubling.outerUnitArc_start S.diagram i j hlen hf p hp
    have h4 : (FaceEdgeDoubling.outerUnitArc S.diagram i j hlen hf p hp).start.val +
        (FaceEdgeDoubling.outerUnitArc S.diagram i j hlen hf p hp).length = p + 1 := by
      rw [h3, FaceEdgeDoubling.outerUnitArc_length S.diagram i j hlen hf p hp]
    exact ⟨jc, le_of_le_of_eq h1 h3.symm, le_of_eq_of_le h4 h2⟩

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
  have hdmem : d ∈ cellDarts S.diagram i := List.mem_toFinset.mp (Finset.mem_sdiff.mp hd).1
  obtain ⟨j, hj⟩ := List.get_of_mem hdmem
  have hdart : FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j = d := by
    rw [FaceEdgeDoubling.dart_eq_get]
    exact hj
  subst hdart
  have hnotRelator := faces_not_mem_of_value S hvalue
  have havoid : ∀ a ∈ S.family, (cell S.diagram i).face ∉ a.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j)) ∉ a.1 := by
    intro a ha
    refine ⟨hnotRelator a ha _ (cell_mem S.diagram i), ?_⟩
    rcases hadj with ⟨i₂, hi₂⟩ | hout
    · rw [hi₂]
      exact hnotRelator a ha _ (cell_mem S.diagram i₂)
    · rw [hout]
      intro hmem
      exact (a.2.boundary.all_gCells _ hmem).1 rfl
  rcases hadj with ⟨i₂, hi₂⟩ | hout
  · have hmem2 : S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j) ∈ cellDarts S.diagram i₂ :=
      ((S.diagram.faceBoundary (cell S.diagram i₂).face).mem_iff _).mpr hi₂
    obtain ⟨q, hq, hget⟩ := List.getElem_of_mem hmem2
    exact false_of_digon_toward_cell S hlegal hmax i j hlen havoid i₂ q hq hget
  · have hmem2 : FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j ∈
        outerDarts S.diagram :=
      List.mem_map.mpr ⟨S.diagram.toCombMap.alpha
          (FaceEdgeDoubling.dart S.diagram (cell S.diagram i).face j),
        List.mem_reverse.mpr (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff _).mpr hout),
        S.diagram.toCombMap.alpha_involutive _⟩
    obtain ⟨p, hp, hget⟩ := List.getElem_of_mem hmem2
    exact false_of_digon_toward_outer S hlegal hmax i j hlen havoid p hp hget

end RealizedSectionFamily
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionCuts.exists_section_of_lt
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.digon_noInternalFaceDart
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.wordNorm_dartWord_nil_le
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.sourceUnitArc_reverseDarts
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.cellUnitArc_boundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.outerUnitArc_boundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.digon_decomposition
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_digon_region
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_digon_toward_cell
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_digon_toward_outer
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_unbound_shared_edge
