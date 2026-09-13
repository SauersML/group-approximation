import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The four sections of a pocket region, and the multiple-edge cut

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a).  Two distinct contiguity regions
between the same two cells cut out a subdiagram `Ξ` with `∂Ξ = s_1 t_1 s_2 t_2`, where `s_1`,
`s_2` are sides of the two regions and `t_1`, `t_2` are arcs of the two cells.  The induction
hypothesis is applied to `Ξ`, which is least area, has fewer cells, and carries these four
sections.  This module proves that half of the step for the pocket of a `PocketRegion`, which
needs no shelling.

* `PocketRegion.boundarySectionCuts`: an exact partition of the inverse boundary cycle of the
  complement into between one and four ambient parts with quasi-geodesic words gives
  `SectionCuts` of the pocket whose sections are the part words, in order.
* `PocketRegion.fourSectionCuts` and `fourSectionCuts_side_short`: the partition
  `s_1 t_1 s_2 t_2`, whose sections `0` and `2` have length at most `ε` when `s_1` and `s_2`
  do.
* `PocketRegion.fourSectionCuts_leastAreaCut`: the pocket of a least-area diagram, with a
  relator cell inside and one outside, is least area, has at least one and fewer relator cells
  than the source, and carries the four sections with short sides.
* `OsinMultipleEdgeCut.ofPocketRegion`: a pocket region of an O-equivalent copy of a
  least-area `Δ` with these four sections, whose regions to `t_1`, `t_2` glue back, is an
  `OsinMultipleEdgeCut` of `Δ`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- **Sections of the pocket from an ambient partition.**  An exact partition of the inverse
boundary cycle of the complement into between one and four ambient parts whose words are
`(λ, c)`-quasi-geodesic gives section cuts of the pocket's boundary word, whose sections are the
part words in order. -/
noncomputable def boundarySectionCuts (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    SectionCuts D lambda c P.diagram.boundaryWord :=
  SectionCuts.ofParts (parts.map (Embedded.dartWord Delta))
    (by rw [P.diagram_boundaryWord, hdecomposition]; exact List.map_flatten)
    (by rw [List.length_map]; exact hpos)
    (by rw [List.length_map]; exact hle)
    (fun part hpart => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpart
      exact hquasi q hq)

/-- The pocket has one section for each part. -/
theorem boundarySectionCuts_count (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    (P.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).count =
      parts.length := by
  show (parts.map (Embedded.dartWord Delta)).length = parts.length
  rw [List.length_map]

/-- Section `j` of the pocket is the word of part `j`. -/
theorem boundarySectionCuts_part (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (j : Fin (P.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).count) :
    (P.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).part j =
      Embedded.dartWord Delta (parts.get (j.cast
        (P.boundarySectionCuts_count D lambda c parts hpos hle hdecomposition hquasi))) := by
  refine (SectionCuts.ofParts_part (parts.map (Embedded.dartWord Delta)) _ _ _ _ j).trans ?_
  simp [List.get_eq_getElem]

/-- Section `j` of the pocket is as long as part `j`. -/
theorem boundarySectionCuts_cut_sub (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (j : Fin (P.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).count) :
    (P.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).cut j.succ -
        (P.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).cut
          j.castSucc =
      (parts.get (j.cast
        (P.boundarySectionCuts_count D lambda c parts hpos hle hdecomposition
          hquasi))).length := by
  refine (SectionCuts.ofParts_cut_sub (parts.map (Embedded.dartWord Delta)) _ _ _ _ j).trans ?_
  simp [List.get_eq_getElem, Embedded.dartWord]

private theorem pocketFourParts_length_pos {α : Type*} (s₁ t₁ s₂ t₂ : List α) :
    0 < [s₁, t₁, s₂, t₂].length := by
  simp

private theorem pocketFourParts_length_le {α : Type*} (s₁ t₁ s₂ t₂ : List α) :
    [s₁, t₁, s₂, t₂].length ≤ 4 := by
  simp

private theorem pocketFourParts_flatten {α : Type*} {x : List α} (s₁ t₁ s₂ t₂ : List α)
    (h : x = s₁ ++ t₁ ++ s₂ ++ t₂) : x = [s₁, t₁, s₂, t₂].flatten := by
  rw [h]
  simp

/-- **Osin's four sections** `s_1 t_1 s_2 t_2` on the pocket, from a partition of the inverse
boundary cycle of the complement into four ambient parts with quasi-geodesic words. -/
noncomputable def fourSectionCuts (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    SectionCuts D lambda c P.diagram.boundaryWord :=
  P.boundarySectionCuts D lambda c [s₁, t₁, s₂, t₂] (pocketFourParts_length_pos s₁ t₁ s₂ t₂)
    (pocketFourParts_length_le s₁ t₁ s₂ t₂)
    (pocketFourParts_flatten s₁ t₁ s₂ t₂ hdecomposition) hquasi

/-- The four-part partition has four sections. -/
theorem fourSectionCuts_count (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count = 4 :=
  P.boundarySectionCuts_count D lambda c [s₁, t₁, s₂, t₂]
    (pocketFourParts_length_pos s₁ t₁ s₂ t₂) (pocketFourParts_length_le s₁ t₁ s₂ t₂)
    (pocketFourParts_flatten s₁ t₁ s₂ t₂ hdecomposition) hquasi

/-- Sections `0` and `2` of the four-part partition, the sides `s_1` and `s_2`, are no longer
than `ε` when the sides are. -/
theorem fourSectionCuts_side_short (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) :
    ∀ j : Fin (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
      ((j : ℕ) = 0 ∨ (j : ℕ) = 2) →
        (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut j.succ -
            (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut
              j.castSucc ≤ eps := by
  have key : ∀ (k : ℕ) (hk : k < 4), (k = 0 ∨ k = 2) →
      ([s₁, t₁, s₂, t₂].get ⟨k, hk⟩).length ≤ eps := by
    intro k hk hk'
    rcases hk' with rfl | rfl
    · exact hs₁
    · exact hs₂
  intro j hj
  refine (P.boundarySectionCuts_cut_sub D lambda c [s₁, t₁, s₂, t₂]
    (pocketFourParts_length_pos s₁ t₁ s₂ t₂) (pocketFourParts_length_le s₁ t₁ s₂ t₂)
    (pocketFourParts_flatten s₁ t₁ s₂ t₂ hdecomposition) hquasi j).trans_le ?_
  exact key j j.isLt hj

/-- **The least-area pocket cut with four sections.**  The pocket of a least-area diagram,
with a relator cell inside the face set and one outside, is least area, has at least one and
fewer relator cells than the source, and carries the four sections `s_1 t_1 s_2 t_2`, of which
the two sides are no longer than `ε`. -/
theorem fourSectionCuts_leastAreaCut (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (hlea : Delta.LeastArea)
    {C C' : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hC : C ∈ Delta.relatorCells) (hCf : C.face ∈ P.faces)
    (hC' : C' ∈ Delta.relatorCells) (hC'f : C'.face ∉ P.faces)
    (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) :
    P.diagram.LeastArea ∧ 0 < P.diagram.rCellCount ∧
      P.diagram.rCellCount < Delta.rCellCount ∧
      (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count = 4 ∧
      ∀ j : Fin (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
        ((j : ℕ) = 0 ∨ (j : ℕ) = 2) →
          (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut j.succ -
              (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut
                j.castSucc ≤ eps :=
  have hcut := P.diagram_leastAreaCut hlea hC hCf hC' hC'f
  ⟨hcut.1, hcut.2.1, hcut.2.2,
    P.fourSectionCuts_count D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi,
    P.fourSectionCuts_side_short D lambda c eps s₁ t₁ s₂ t₂ hdecomposition hquasi hs₁ hs₂⟩

end PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

open Embedded in
/-- **The multiple-edge cut from a pocket region** (input G2 of lane `hull-select`, assembly).
Let `Δ` be least area and `Δ'` an O-equivalent copy, such as the optimal diagram of a globally
distinguished family.  Take a pocket region of `Δ'` with a relator cell inside and one outside,
with the inverse boundary cycle of its complement split as `s_1 t_1 s_2 t_2` into parts with
`(λ, c)`-quasi-geodesic words and the sides `s_1`, `s_2` no longer than `ε`.  The pocket is a cut
of `Δ` as soon as regions to `t_1` and `t_2` in O-equivalent copies of the pocket glue back into
cell-to-cell regions of O-equivalent copies of `Δ'`. -/
noncomputable def OsinMultipleEdgeCut.ofPocketRegion {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Delta Delta' : DiscDiagram.{u, w, v} W}
    (equiv : OEquivalentDiscDiagram Delta Delta') (hlea : Delta.LeastArea)
    (P : PocketRegion Delta')
    {C C' : RelatorCell Delta'.toCombMap Delta'.outerFace W}
    (hC : C ∈ Delta'.relatorCells) (hCf : C.face ∈ P.faces)
    (hC' : C' ∈ Delta'.relatorCells) (hC'f : C'.face ∉ P.faces)
    (s₁ t₁ s₂ t₂ : List Delta'.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta' P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta' part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (htransport :
      ∀ j : Fin (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
        ((j : ℕ) = 1 ∨ (j : ℕ) = 3) →
          ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
            ∀ a : RegionCandidate D eps Xi,
              RegionCandidate.TargetsSectionIndex
                  (P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi) j a →
                ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                  (t : Fin Y.rCellCount),
                  Nonempty (OEquivalentDiscDiagram Delta' Y) ∧
                    b.2.target = some t ∧ b.2.source ≠ t ∧
                    b.contiguityDegree = a.contiguityDegree) :
    OsinMultipleEdgeCut D lambda c eps Delta :=
  have key := P.fourSectionCuts_leastAreaCut D lambda c eps (equiv.leastArea hlea) hC hCf hC'
    hC'f s₁ t₁ s₂ t₂ hdecomposition hquasi hs₁ hs₂
  { enclosed := P.diagram
    leastArea := key.1
    rCellCount_pos := key.2.1
    rCellCount_lt := lt_of_lt_of_eq key.2.2.1 equiv.rCellCount_eq
    sections := P.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi
    count_eq := key.2.2.2.1
    side_short := key.2.2.2.2
    transport := by
      intro j hj Xi E a ha
      obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne, hdeg⟩ := htransport j hj Xi E a ha
      exact ⟨Y, b, t, ⟨equiv.trans EY⟩, htarget, hne, hdeg⟩ }

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.boundarySectionCuts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.boundarySectionCuts_count
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.boundarySectionCuts_part
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.boundarySectionCuts_cut_sub
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.fourSectionCuts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.fourSectionCuts_count
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.fourSectionCuts_side_short
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.fourSectionCuts_leastAreaCut
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCut.ofPocketRegion
