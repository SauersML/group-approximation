import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The loop cut from a pocket region

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "it is easy to show that `Φ_M` can not
contain loops either.  The only difference is that the subdiagram `Ξ` will be bounded by `st`,
where `l(s) < ε` and `t` is a subpath of `∂Π_1`."  A pocket with a relator cell inside, whose
inverse complement cycle reads a side `s` and an arc `t` of a cell `Π_1` outside read backwards,
with side value of word norm at most `ε`, is cut out by a collar of a geodesic word along `s`.
The collared pocket is a least-area cut with two sections, and regions to `t` glue back into
cell-to-cell regions.  This is the collar step of case (b) of the one-cell Case 1 of Lemma 9.4.

* `PocketRegion.twoSectionCuts` and `twoSectionCuts_side_short`: the partition `s t`, whose
  section `0` has length at most `ε` when `s` does.
* `OsinLoopCut.ofPocketRegion`: a pocket region of an O-equivalent copy of a least-area `Δ` with
  these two sections, whose regions to `t` glue back, is an `OsinLoopCut` of `Δ`.
* `PocketRegion.twoSectionCuts_cellTransport`: the transport of section `1`, from
  `PocketCellTransportStatement` (lane `go-lemma42`) at `pre = s`.
* `nonempty_osinLoopCut_of_pocketRegion`: the loop cut from a pocket region of an O-equivalent
  copy with legal labels, from `GeodesicCollarStatement` (lane `kh-torsion`, through
  `PocketRegion.exists_twoCollars_of_ne_or` with an empty second side and arc) and
  `PocketCellTransportStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7); certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

section Pieces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace PocketRegion

variable {Delta : DiscDiagram.{u, w, v} W}

private theorem pocketTwoParts_length_pos {α : Type*} (s t : List α) : 0 < [s, t].length := by
  simp

private theorem pocketTwoParts_length_le {α : Type*} (s t : List α) : [s, t].length ≤ 4 := by
  simp

private theorem pocketTwoParts_flatten {α : Type*} {x : List α} (s t : List α)
    (h : x = s ++ t) : x = [s, t].flatten := by
  rw [h]
  simp

/-- **Osin's two sections** `s t` on the pocket, from a partition of the inverse boundary cycle of
the complement into two ambient parts with quasi-geodesic words. -/
noncomputable def twoSectionCuts (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (s t : List Delta.toCombMap.Dart)
    (hdecomposition : invDarts Delta P.outer.cycle = s ++ t)
    (hquasi : ∀ part ∈ [s, t], IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta part)) :
    SectionCuts D lambda c P.diagram.boundaryWord :=
  P.boundarySectionCuts D lambda c [s, t] (pocketTwoParts_length_pos s t)
    (pocketTwoParts_length_le s t) (pocketTwoParts_flatten s t hdecomposition) hquasi

/-- The two-part partition has two sections. -/
theorem twoSectionCuts_count (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (s t : List Delta.toCombMap.Dart)
    (hdecomposition : invDarts Delta P.outer.cycle = s ++ t)
    (hquasi : ∀ part ∈ [s, t], IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta part)) :
    (P.twoSectionCuts D lambda c s t hdecomposition hquasi).count = 2 :=
  P.boundarySectionCuts_count D lambda c [s, t] (pocketTwoParts_length_pos s t)
    (pocketTwoParts_length_le s t) (pocketTwoParts_flatten s t hdecomposition) hquasi

/-- Section `0` of the two-part partition, the side `s`, is no longer than `ε` when the side
is. -/
theorem twoSectionCuts_side_short (P : PocketRegion Delta) (D : RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (s t : List Delta.toCombMap.Dart)
    (hdecomposition : invDarts Delta P.outer.cycle = s ++ t)
    (hquasi : ∀ part ∈ [s, t], IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta part))
    (hs : s.length ≤ eps) :
    ∀ j : Fin (P.twoSectionCuts D lambda c s t hdecomposition hquasi).count, (j : ℕ) = 0 →
      (P.twoSectionCuts D lambda c s t hdecomposition hquasi).cut j.succ -
          (P.twoSectionCuts D lambda c s t hdecomposition hquasi).cut j.castSucc ≤ eps := by
  have key : ∀ (k : ℕ) (hk : k < 2), k = 0 → ([s, t].get ⟨k, hk⟩).length ≤ eps := by
    intro k hk hk'
    subst hk'
    exact hs
  intro j hj
  refine (P.boundarySectionCuts_cut_sub D lambda c [s, t] (pocketTwoParts_length_pos s t)
    (pocketTwoParts_length_le s t) (pocketTwoParts_flatten s t hdecomposition) hquasi
    j).trans_le ?_
  exact key j j.isLt hj

end PocketRegion

/-- **The loop cut from a pocket region** (input G2 of lane `hull-select`, loop case).  Let `Δ` be
least area and `Δ'` an O-equivalent copy.  Take a pocket region of `Δ'` with a relator cell inside
and one outside, with the inverse boundary cycle of its complement split as `s t` into parts with
`(λ, c)`-quasi-geodesic words and the side `s` no longer than `ε`.  The pocket is a loop cut of
`Δ` as soon as regions to `t` in O-equivalent copies of the pocket glue back into cell-to-cell
regions of O-equivalent copies of `Δ'`. -/
noncomputable def OsinLoopCut.ofPocketRegion {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Delta Delta' : DiscDiagram.{u, w, v} W}
    (equiv : OEquivalentDiscDiagram Delta Delta') (hlea : Delta.LeastArea)
    (P : PocketRegion Delta')
    {C C' : RelatorCell Delta'.toCombMap Delta'.outerFace W}
    (hC : C ∈ Delta'.relatorCells) (hCf : C.face ∈ P.faces)
    (hC' : C' ∈ Delta'.relatorCells) (hC'f : C'.face ∉ P.faces)
    (s t : List Delta'.toCombMap.Dart)
    (hdecomposition : invDarts Delta' P.outer.cycle = s ++ t)
    (hquasi : ∀ part ∈ [s, t], IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta' part))
    (hs : s.length ≤ eps)
    (htransport :
      ∀ j : Fin (P.twoSectionCuts D lambda c s t hdecomposition hquasi).count, (j : ℕ) = 1 →
        ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
          ∀ a : RegionCandidate D eps Xi,
            RegionCandidate.TargetsSectionIndex
                (P.twoSectionCuts D lambda c s t hdecomposition hquasi) j a →
              ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                (k : Fin Y.rCellCount),
                Nonempty (OEquivalentDiscDiagram Delta' Y) ∧
                  b.2.target = some k ∧ b.2.source ≠ k ∧
                  b.contiguityDegree = a.contiguityDegree) :
    OsinLoopCut D lambda c eps Delta :=
  have hcut := P.diagram_leastAreaCut (equiv.leastArea hlea) hC hCf hC' hC'f
  { enclosed := P.diagram
    leastArea := hcut.1
    rCellCount_pos := hcut.2.1
    rCellCount_lt := lt_of_lt_of_eq hcut.2.2 equiv.rCellCount_eq
    sections := P.twoSectionCuts D lambda c s t hdecomposition hquasi
    count_eq := P.twoSectionCuts_count D lambda c s t hdecomposition hquasi
    side_short := P.twoSectionCuts_side_short D lambda c eps s t hdecomposition hquasi hs
    transport := by
      intro j hj Xi E a ha
      obtain ⟨Y, b, k, ⟨EY⟩, htarget, hne, hdeg⟩ := htransport j hj Xi E a ha
      exact ⟨Y, b, k, ⟨equiv.trans EY⟩, htarget, hne, hdeg⟩ }

private theorem loopPartsCut_map_label {α β : Type*} (f : α → β) (parts : List (List α))
    (k : ℕ) :
    CutSections.partsCut (parts.map (List.map f)) k = CutSections.partsCut parts k := by
  unfold CutSections.partsCut
  rw [← List.map_take, ← List.map_flatten, List.length_map]

private theorem partsCut_two_first {α : Type*} (a b : List α) :
    CutSections.partsCut [a, b] 1 = a.length := by
  simp [CutSections.partsCut]

private theorem partsCut_two_second {α : Type*} (a b : List α) :
    CutSections.partsCut [a, b] (1 + 1) = a.length + b.length := by
  simp [CutSections.partsCut]

namespace PocketRegion

/-- **The cell transport of the loop cut.**  Let the inverse complement cycle of a pocket region
of `X` split as `s t`, with `t` an arc of a cell `i` outside the pocket read backwards, and both
parts quasi-geodesic.  A region of an O-equivalent copy of the pocket to section `1` of the two
sections glues back into a region of an O-equivalent copy of `X` from a cell to another cell,
with the same contiguity degree. -/
theorem twoSectionCuts_cellTransport (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (P : PocketRegion X) (hout : P.outer.FollowsBoundary)
    {i : Fin X.rCellCount} (hi : (cell X i).face ∉ P.faces)
    (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle = s ++ invDarts X A.darts)
    (hquasi : ∀ part ∈ [s, invDarts X A.darts],
      IsLambdaCQuasiGeodesicWord D lambda c (dartWord X part)) :
    ∀ k : Fin (P.twoSectionCuts D lambda c s (invDarts X A.darts) hdecomposition hquasi).count,
      (k : ℕ) = 1 →
        ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
          ∀ a : RegionCandidate D eps Xi,
            RegionCandidate.TargetsSectionIndex
                (P.twoSectionCuts D lambda c s (invDarts X A.darts) hdecomposition hquasi) k a →
              ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                (t : Fin Y.rCellCount),
                Nonempty (OEquivalentDiscDiagram X Y) ∧ b.2.target = some t ∧
                  b.2.source ≠ t ∧ b.contiguityDegree = a.contiguityDegree := by
  have hcut : ∀ k : Fin ((P.twoSectionCuts D lambda c s (invDarts X A.darts) hdecomposition
      hquasi).count + 1),
      (P.twoSectionCuts D lambda c s (invDarts X A.darts) hdecomposition hquasi).cut k =
        CutSections.partsCut [s, invDarts X A.darts] k :=
    fun k => loopPartsCut_map_label X.label [s, invDarts X A.darts] k
  have hinv : (invDarts X A.darts).length = A.length := by
    rw [invDarts, List.length_map, List.length_reverse, CyclicArc.darts_length]
  intro k hk Xi E a ha
  obtain ⟨hnone, hlo, hhi⟩ := ha
  rw [hcut, Fin.val_castSucc, hk, partsCut_two_first] at hlo
  rw [hcut, Fin.val_succ, hk, partsCut_two_second, hinv] at hhi
  exact hcell D eps W X P hout i hi A s []
    (by simp only [hdecomposition, List.append_nil]) Xi E a hnone hlo hhi

end PocketRegion

/-- **The loop cut from a pocket region.**  Let `Δ` be least area and `X` an O-equivalent copy
with labels in the symmetric label alphabet.  Take a pocket region of `X`, both cycles following
the boundary, with a relator cell inside and a cell `i` outside.  Let its inverse complement cycle
read a side `s` and an arc of `i` backwards, with side value of word norm at most `ε`.  Under
`C(ε, μ, λ, c, ρ)` with `λ ≤ 1` and `0 ≤ c`, the collar and the cell transport give a loop cut
of `Δ`. -/
theorem nonempty_osinLoopCut_of_pocketRegion
    (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    {Delta X : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (equiv : OEquivalentDiscDiagram Delta X)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (P : PocketRegion X) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ P.faces) {i : Fin X.rCellCount} (hi : (cell X i).face ∉ P.faces)
    (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle = s ++ invDarts X A.darts)
    (hnorm : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps) :
    Nonempty (OsinLoopCut D lambda c eps Delta) := by
  -- The side and the arc, with an empty second side and arc.
  have hdecomposition' : invDarts X P.outer.cycle = s ++ invDarts X A.darts ++ [] ++ [] := by
    simp only [hdecomposition, List.append_nil]
  have hne := P.ne_or_of_leastArea (equiv.leastArea hlea) hC hCf hdecomposition'
  obtain ⟨g, hgeo, hq⟩ := exists_geodesicWord_isLambdaCQuasiGeodesicWord D
    (RelLetter.listVal (dartWord X s)) hlambda hc
  have hnil : s = [] → g = [] := fun hs => List.eq_nil_of_length_eq_zero (by
    rw [hgeo.2.2, hs]
    simp only [dartWord, List.map_nil, RelLetter.listVal_nil, wordDist_self])
  obtain ⟨Y, E, Q, c₁, c₂, ι, -, -, houtQ, hdecQ, hword₁, hword₂, halpha, -, -, hcellsQ,
      hfacesQ⟩ :=
    PocketRegion.exists_twoCollars_of_ne_or hcollar (symmetricLabelAlphabet D)
      (symmetricLabelAlphabet.symmetric D) hlabel P hin hout hdecomposition' hne (g₂ := [])
      (fun l hl => symmetricLabelAlphabet.isLetter D (hgeo.1 l hl)) (by simp)
      ((one_mul _).symm.trans hgeo.2.1) rfl hnil (fun _ => rfl)
  -- The second collar is empty.
  have hc₂ : c₂ = [] := by
    have h := congrArg List.length hword₂
    simp only [dartWord, List.length_map, List.length_nil] at h
    exact List.eq_nil_of_length_eq_zero h
  -- The arc of `i` on the collared copy.
  have hinvmap : ∀ l : List X.toCombMap.Dart, invDarts Y (l.map ι) = (invDarts X l).map ι := by
    intro l
    simp only [invDarts, List.map_reverse, List.map_map, Function.comp_def, halpha]
  obtain ⟨B, hB⟩ : ∃ B : CyclicArc (cellDarts Y (E.cellIndex i)),
      invDarts Y B.darts = (invDarts X A.darts).map ι :=
    ⟨A.mapTo ι (hcellsQ i ((P.mem_outside_iff _).mpr hi)), by
      rw [CyclicArc.mapTo_darts, hinvmap]⟩
  have hdecB : invDarts Y Q.outer.cycle = c₁ ++ invDarts Y B.darts := by
    rw [hdecQ, hB, hc₂]
    simp only [List.map_nil, List.append_nil]
  -- The kept cell stays inside, and `i` stays outside.
  obtain ⟨k, hk⟩ := List.get_of_mem hC
  have hkQ : (cell Y (E.cellIndex k)).face ∈ Q.faces := by
    refine (hfacesQ k).mpr ?_
    rw [show cell X k = C from hk]
    exact hCf
  have hiQ : (cell Y (E.cellIndex i)).face ∉ Q.faces := fun h => hi ((hfacesQ i).mp h)
  -- Both parts are quasi-geodesic, and the collared side is short.
  have hquasi : ∀ part ∈ [c₁, invDarts Y B.darts],
      IsLambdaCQuasiGeodesicWord D lambda c (dartWord Y part) := by
    intro part hpart
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
    rcases hpart with rfl | rfl
    · rw [hword₁]
      exact hq
    · exact CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hcondition B
  have hc₁ : c₁.length ≤ eps := by
    have h := congrArg List.length hword₁
    simp only [dartWord, List.length_map] at h
    rw [h, hgeo.2.2, wordDist_one_left]
    exact hnorm
  exact ⟨OsinLoopCut.ofPocketRegion (equiv.trans E) hlea Q (cell_mem Y (E.cellIndex k)) hkQ
    (cell_mem Y (E.cellIndex i)) hiQ c₁ (invDarts Y B.darts) hdecB hquasi hc₁
    (PocketRegion.twoSectionCuts_cellTransport hcell Q houtQ hiQ B c₁ hdecB hquasi)⟩

end Pieces

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.twoSectionCuts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.twoSectionCuts_count
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.twoSectionCuts_side_short
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLoopCut.ofPocketRegion
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.twoSectionCuts_cellTransport
#audit_axioms GroupApproximation.GGT.VanKampen.nonempty_osinLoopCut_of_pocketRegion
