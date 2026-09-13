import GroupApproximation.GGT.VanKampen.SurgeryCutSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLeastAreaCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutSections
import GroupApproximation.Meta.AxiomGuard

/-!
# The least-area pocket cut with four sections

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a).  Two distinct
contiguity regions between the same two cells cut out a subdiagram `Ξ` with
`∂Ξ = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions and `t_1`,
`t_2` are arcs of the two cells.  The induction hypothesis is applied to `Ξ`, which
is least area, has fewer cells, and carries these four sections.  This module
proves that half of the step for the piece of a `Surgery.MapCollapse.RegionCutData`.

* `RegionCutData.diagram_boundaryWord`: the piece reads the word along the inverse
  of the cut-away region's boundary cycle.
* `RegionCutData.boundarySectionCuts`: an exact partition of that walk into between
  one and four ambient parts with quasi-geodesic words gives `SectionCuts` of the
  piece whose sections are the part words, in order.
* `RegionCutData.fourSectionCuts` and `fourSectionCuts_side_short`: the partition
  `s_1 t_1 s_2 t_2`, whose sections `0` and `2` have length at most `ε` when `s_1`
  and `s_2` do.
* `RegionCutData.fourSectionCuts_leastAreaCut`: the piece of a least-area diagram is
  least area, has at least one and fewer relator cells than the source, and carries
  the four sections with short sides.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe u w v

namespace RegionCutData

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- The piece a cut encloses reads the word along the inverse of the cut-away
region's boundary cycle. -/
theorem diagram_boundaryWord (cut : RegionCutData Delta) :
    cut.diagram.boundaryWord =
      Embedded.dartWord Delta (Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle) := by
  have h := congrArg (List.map Delta.label) cut.diagram_outerDarts_map_val
  rw [List.map_map] at h
  rw [← Embedded.dartWord_outerDarts cut.diagram]
  exact h

/-- **Sections of the piece from an ambient partition.**  An exact partition of the
inverse boundary cycle into between one and four ambient parts whose words are
`(λ, c)`-quasi-geodesic gives section cuts of the piece's boundary word, whose
sections are the part words in order. -/
noncomputable def boundarySectionCuts (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    SectionCuts D lambda c cut.diagram.boundaryWord :=
  SectionCuts.ofParts (parts.map (Embedded.dartWord Delta))
    (by rw [cut.diagram_boundaryWord, hdecomposition]; exact List.map_flatten)
    (by rw [List.length_map]; exact hpos)
    (by rw [List.length_map]; exact hle)
    (fun part hpart => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpart
      exact hquasi q hq)

/-- The piece has one section for each part. -/
theorem boundarySectionCuts_count (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    (cut.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).count =
      parts.length := by
  show (parts.map (Embedded.dartWord Delta)).length = parts.length
  rw [List.length_map]

/-- Section `j` of the piece is the word of part `j`. -/
theorem boundarySectionCuts_part (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (j : Fin (cut.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).count) :
    (cut.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).part j =
      Embedded.dartWord Delta (parts.get (j.cast
        (cut.boundarySectionCuts_count D lambda c parts hpos hle hdecomposition hquasi))) := by
  refine (SectionCuts.ofParts_part (parts.map (Embedded.dartWord Delta)) _ _ _ _ j).trans ?_
  simp [List.get_eq_getElem]

/-- Section `j` of the piece is as long as part `j`. -/
theorem boundarySectionCuts_cut_sub (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (parts : List (List Delta.toCombMap.Dart))
    (hpos : 0 < parts.length) (hle : parts.length ≤ 4)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      parts.flatten)
    (hquasi : ∀ part ∈ parts,
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (j : Fin (cut.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).count) :
    (cut.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).cut j.succ -
        (cut.boundarySectionCuts D lambda c parts hpos hle hdecomposition hquasi).cut
          j.castSucc =
      (parts.get (j.cast
        (cut.boundarySectionCuts_count D lambda c parts hpos hle hdecomposition
          hquasi))).length := by
  refine (SectionCuts.ofParts_cut_sub (parts.map (Embedded.dartWord Delta)) _ _ _ _ j).trans ?_
  simp [List.get_eq_getElem, Embedded.dartWord]

private theorem fourParts_length_pos {α : Type*} (s₁ t₁ s₂ t₂ : List α) :
    0 < [s₁, t₁, s₂, t₂].length := by
  simp

private theorem fourParts_length_le {α : Type*} (s₁ t₁ s₂ t₂ : List α) :
    [s₁, t₁, s₂, t₂].length ≤ 4 := by
  simp

private theorem fourParts_flatten {α : Type*} {x : List α} (s₁ t₁ s₂ t₂ : List α)
    (h : x = s₁ ++ t₁ ++ s₂ ++ t₂) : x = [s₁, t₁, s₂, t₂].flatten := by
  rw [h]
  simp

/-- **Osin's four sections** `s_1 t_1 s_2 t_2` on the piece, from a partition of the
inverse boundary cycle into four ambient parts with quasi-geodesic words. -/
noncomputable def fourSectionCuts (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    SectionCuts D lambda c cut.diagram.boundaryWord :=
  cut.boundarySectionCuts D lambda c [s₁, t₁, s₂, t₂] (fourParts_length_pos s₁ t₁ s₂ t₂)
    (fourParts_length_le s₁ t₁ s₂ t₂) (fourParts_flatten s₁ t₁ s₂ t₂ hdecomposition) hquasi

/-- The four-part partition has four sections. -/
theorem fourSectionCuts_count (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part)) :
    (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count = 4 :=
  cut.boundarySectionCuts_count D lambda c [s₁, t₁, s₂, t₂]
    (fourParts_length_pos s₁ t₁ s₂ t₂) (fourParts_length_le s₁ t₁ s₂ t₂)
    (fourParts_flatten s₁ t₁ s₂ t₂ hdecomposition) hquasi

/-- Sections `0` and `2` of the four-part partition, the sides `s_1` and `s_2`, are no
longer than `ε` when the sides are. -/
theorem fourSectionCuts_side_short (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) :
    ∀ j : Fin (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
      ((j : ℕ) = 0 ∨ (j : ℕ) = 2) →
        (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut j.succ -
            (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut
              j.castSucc ≤ eps := by
  have key : ∀ (k : ℕ) (hk : k < 4), (k = 0 ∨ k = 2) →
      ([s₁, t₁, s₂, t₂].get ⟨k, hk⟩).length ≤ eps := by
    intro k hk hk'
    rcases hk' with rfl | rfl
    · exact hs₁
    · exact hs₂
  intro j hj
  refine (cut.boundarySectionCuts_cut_sub D lambda c [s₁, t₁, s₂, t₂]
    (fourParts_length_pos s₁ t₁ s₂ t₂) (fourParts_length_le s₁ t₁ s₂ t₂)
    (fourParts_flatten s₁ t₁ s₂ t₂ hdecomposition) hquasi j).trans_le ?_
  exact key j j.isLt hj

/-- **The least-area cut with four sections.**  The piece a cut encloses in a
least-area diagram, when it keeps at least one relator cell, is least area, has at
least one and fewer relator cells than the source, and carries the four sections
`s_1 t_1 s_2 t_2`, of which the two sides are no longer than `ε`. -/
theorem fourSectionCuts_leastAreaCut (cut : RegionCutData Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (hlea : Delta.LeastArea) (hcells : 0 < cut.cells.length)
    (s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle =
      s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) :
    cut.diagram.LeastArea ∧ 0 < cut.diagram.rCellCount ∧
      cut.diagram.rCellCount < Delta.rCellCount ∧
      (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count = 4 ∧
      ∀ j : Fin (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
        ((j : ℕ) = 0 ∨ (j : ℕ) = 2) →
          (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut j.succ -
              (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).cut
                j.castSucc ≤ eps := by
  refine ⟨cut.diagram_leastArea hlea, ?_, cut.diagram_rCellCount_lt,
    cut.fourSectionCuts_count D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi,
    cut.fourSectionCuts_side_short D lambda c eps s₁ t₁ s₂ t₂ hdecomposition hquasi hs₁ hs₂⟩
  rw [cut.diagram_rCellCount]
  exact hcells

end RegionCutData

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.diagram_boundaryWord
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.boundarySectionCuts
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.boundarySectionCuts_count
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.boundarySectionCuts_part
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.boundarySectionCuts_cut_sub
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.fourSectionCuts
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.fourSectionCuts_count
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.fourSectionCuts_side_short
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.fourSectionCuts_leastAreaCut
