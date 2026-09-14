import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoCollars
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSide
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerParts
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.GGT.VanKampen.GeodesicQuasiGeodesic
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge cut from the pocket pieces

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Two distinct selected regions joining the
same two cells `Π_i ≠ Π_j` enclose a pocket with a relator cell inside; a pocket without one merges
the two regions (`zeroCellPocketMerge`), which the producer of the pocket region uses.  The inverse
complement cycle of the pocket reads `s_1 t_1 s_2 t_2`, with `t_1`, `t_2` arcs of `Π_i`, `Π_j`
read backwards and sides of word norm at most `ε`.  A collar of geodesic words along both sides
makes all four parts quasi-geodesic, so the collared pocket is a least-area cut with four sections,
and regions to `t_1` and `t_2` glue back into cell-to-cell regions.

* `PocketRegion.ne_or_of_leastArea`: in a least-area diagram, a pocket with a relator cell inside
  has a nonempty arc or a side of value `≠ 1`.
* `nonempty_osinMultipleEdgeCut_of_pocketRegion`: the cut from a pocket region of an O-equivalent
  copy with legal labels, from `GeodesicCollarStatement` (lane `kh-torsion`, through
  `PocketRegion.exists_twoCollars_of_ne_or`) and `PocketCellTransportStatement` (lane
  `go-lemma42`, through `PocketRegion.fourSectionCuts_cellTransport`).
* `multipleEdgeCutInput_of_pieces`: `MultipleEdgeCutInput` from `MultipleEdgePocketRegionInput`
  (lane `kh-ejz`) and the two statements.
* `OsinMultipleEdgePocketRegionSectionStatement` and `osinMultipleEdgeCutSection_of_pieces`: the
  same uniformly in the parameters, giving `OsinMultipleEdgeCutSectionStatement`.

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

/-- **A pocket with a relator cell in a least-area diagram has a nonempty arc or a nontrivial
side.**  Otherwise its inverse complement cycle reads `s_1 s_2` of value `1`, which the empty
relator product fills, against the relator cell inside. -/
theorem ne_or_of_leastArea {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (P : PocketRegion Delta) {C : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hC : C ∈ Delta.relatorCells) (hCf : C.face ∈ P.faces)
    {s₁ t₁ s₂ t₂ : List Delta.toCombMap.Dart}
    (hdecomposition : invDarts Delta P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂) :
    t₁ ≠ [] ∨ t₂ ≠ [] ∨ RelLetter.listVal (dartWord Delta s₁) ≠ 1 ∨
      RelLetter.listVal (dartWord Delta s₂) ≠ 1 := by
  by_contra h
  obtain ⟨ht₁, h⟩ := not_or.mp h
  obtain ⟨ht₂, h⟩ := not_or.mp h
  obtain ⟨hs₁, hs₂⟩ := not_or.mp h
  have hs₁' := not_not.mp hs₁
  have hs₂' := not_not.mp hs₂
  simp only [dartWord, RelLetter.listVal] at hs₁' hs₂'
  have hvalue : P.diagram.boundaryValue = 1 := by
    show RelLetter.listVal P.diagram.boundaryWord = 1
    rw [P.diagram_boundaryWord, hdecomposition, not_not.mp ht₁, not_not.mp ht₂]
    simp only [dartWord, RelLetter.listVal, List.append_nil, List.map_append, List.prod_append,
      hs₁', hs₂', one_mul]
  have hzero : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) 0
      P.diagram.boundaryValue := by
    rw [hvalue]
    exact RelatorDefectBudget.IsRelatorProduct.one
  have hle : P.diagram.rCellCount ≤ 0 := P.diagram_leastArea hlea hzero
  have hpos := P.diagram_rCellCount_pos hC hCf
  omega

end PocketRegion

/-- **The multiple-edge cut from a pocket region.**  Let `Δ` be least area and `X` an O-equivalent
copy with labels in the symmetric label alphabet.  Take a pocket region of `X`, both cycles
following the boundary, with a relator cell inside and cells `i`, `j` outside.  Let its inverse
complement cycle read a side `s_1`, an arc of `i` backwards, a side `s_2` and an arc of `j`
backwards, with side values of word norm at most `ε`.  Under `C(ε, μ, λ, c, ρ)` with `λ ≤ 1` and
`0 ≤ c`, the collar and the cell transport give a multiple-edge cut of `Δ`. -/
theorem nonempty_osinMultipleEdgeCut_of_pocketRegion
    (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    {Delta X : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (equiv : OEquivalentDiscDiagram Delta X)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (P : PocketRegion X) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ P.faces) {i j : Fin X.rCellCount} (hi : (cell X i).face ∉ P.faces)
    (hj : (cell X j).face ∉ P.faces) (A₁ : CyclicArc (cellDarts X i))
    (A₂ : CyclicArc (cellDarts X j)) (s₁ s₂ : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle =
      s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hnorm₁ : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₁)) ≤ eps)
    (hnorm₂ : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₂)) ≤ eps) :
    Nonempty (OsinMultipleEdgeCut D lambda c eps Delta) := by
  have hne := P.ne_or_of_leastArea (equiv.leastArea hlea) hC hCf hdecomposition
  obtain ⟨g₁, hgeo₁, hq₁⟩ := exists_geodesicWord_isLambdaCQuasiGeodesicWord D
    (RelLetter.listVal (dartWord X s₁)) hlambda hc
  obtain ⟨g₂, hgeo₂, hq₂⟩ := exists_geodesicWord_isLambdaCQuasiGeodesicWord D
    (RelLetter.listVal (dartWord X s₂)) hlambda hc
  have hnil₁ : s₁ = [] → g₁ = [] := fun hs => List.eq_nil_of_length_eq_zero (by
    rw [hgeo₁.2.2, hs]
    simp only [dartWord, List.map_nil, RelLetter.listVal_nil, wordDist_self])
  have hnil₂ : s₂ = [] → g₂ = [] := fun hs => List.eq_nil_of_length_eq_zero (by
    rw [hgeo₂.2.2, hs]
    simp only [dartWord, List.map_nil, RelLetter.listVal_nil, wordDist_self])
  obtain ⟨Y, E, Q, c₁, c₂, ι, -, -, houtQ, hdecQ, hword₁, hword₂, halpha, -, -, hcellsQ,
      hfacesQ⟩ :=
    PocketRegion.exists_twoCollars_of_ne_or hcollar (symmetricLabelAlphabet D)
      (symmetricLabelAlphabet.symmetric D) hlabel P hin hout hdecomposition hne
      (fun l hl => symmetricLabelAlphabet.isLetter D (hgeo₁.1 l hl))
      (fun l hl => symmetricLabelAlphabet.isLetter D (hgeo₂.1 l hl))
      ((one_mul _).symm.trans hgeo₁.2.1) ((one_mul _).symm.trans hgeo₂.2.1) hnil₁ hnil₂
  -- The arcs of `i` and `j` on the collared copy.
  have hinvmap : ∀ l : List X.toCombMap.Dart, invDarts Y (l.map ι) = (invDarts X l).map ι := by
    intro l
    simp only [invDarts, List.map_reverse, List.map_map, Function.comp_def, halpha]
  obtain ⟨B₁, hB₁⟩ : ∃ B : CyclicArc (cellDarts Y (E.cellIndex i)),
      invDarts Y B.darts = (invDarts X A₁.darts).map ι :=
    ⟨A₁.mapTo ι (hcellsQ i ((P.mem_outside_iff _).mpr hi)), by
      rw [CyclicArc.mapTo_darts, hinvmap]⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B : CyclicArc (cellDarts Y (E.cellIndex j)),
      invDarts Y B.darts = (invDarts X A₂.darts).map ι :=
    ⟨A₂.mapTo ι (hcellsQ j ((P.mem_outside_iff _).mpr hj)), by
      rw [CyclicArc.mapTo_darts, hinvmap]⟩
  have hdecB : invDarts Y Q.outer.cycle =
      c₁ ++ invDarts Y B₁.darts ++ c₂ ++ invDarts Y B₂.darts := by
    rw [hdecQ, hB₁, hB₂]
  -- The kept cell stays inside, and `i`, `j` stay outside.
  obtain ⟨k, hk⟩ := List.get_of_mem hC
  have hkQ : (cell Y (E.cellIndex k)).face ∈ Q.faces := by
    refine (hfacesQ k).mpr ?_
    rw [show cell X k = C from hk]
    exact hCf
  have hiQ : (cell Y (E.cellIndex i)).face ∉ Q.faces := fun h => hi ((hfacesQ i).mp h)
  have hjQ : (cell Y (E.cellIndex j)).face ∉ Q.faces := fun h => hj ((hfacesQ j).mp h)
  -- The four parts are quasi-geodesic, and the collared sides are short.
  have hquasi : ∀ part ∈ [c₁, invDarts Y B₁.darts, c₂, invDarts Y B₂.darts],
      IsLambdaCQuasiGeodesicWord D lambda c (dartWord Y part) := by
    intro part hpart
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
    rcases hpart with rfl | rfl | rfl | rfl
    · rw [hword₁]
      exact hq₁
    · exact CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hcondition B₁
    · rw [hword₂]
      exact hq₂
    · exact CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hcondition B₂
  have hc₁ : c₁.length ≤ eps := by
    have h := congrArg List.length hword₁
    simp only [dartWord, List.length_map] at h
    rw [h, hgeo₁.2.2, wordDist_one_left]
    exact hnorm₁
  have hc₂ : c₂.length ≤ eps := by
    have h := congrArg List.length hword₂
    simp only [dartWord, List.length_map] at h
    rw [h, hgeo₂.2.2, wordDist_one_left]
    exact hnorm₂
  exact ⟨OsinMultipleEdgeCut.ofPocketRegion (equiv.trans E) hlea Q (cell_mem Y (E.cellIndex k))
    hkQ (cell_mem Y (E.cellIndex i)) hiQ c₁ (invDarts Y B₁.darts) c₂ (invDarts Y B₂.darts) hdecB
    hquasi hc₁ hc₂
    (PocketRegion.fourSectionCuts_cellTransport hcell Q houtQ hiQ hjQ B₁ B₂ c₁ c₂ hdecB hquasi)⟩

/-- **G2, multiple edges, from the pocket pieces.**  Under `C(ε, μ, λ, c, ρ)` with `λ ≤ 1` and
`0 ≤ c`, `MultipleEdgePocketRegionInput` (lane `kh-ejz`), `GeodesicCollarStatement` (lane
`kh-torsion`) and `PocketCellTransportStatement` (lane `go-lemma42`) give `MultipleEdgeCutInput`.
The zero-cell merge enters through the producer of the pocket region. -/
theorem multipleEdgeCutInput_of_pieces (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hpocket : MultipleEdgePocketRegionInput.{u, w, v} D lambda c eps W) :
    MultipleEdgeCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨X, ⟨E⟩, hlabel, P, C, i', j', s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdecomposition, hnorm₁,
      hnorm₂, hin, hout⟩ := hpocket Delta cuts hlea S a ha b hb hab i j hij hai hbi
  exact nonempty_osinMultipleEdgeCut_of_pocketRegion hcollar hcell hcondition hlambda hc hlea E
    hlabel P hin hout hC hCf hi hj A₁ A₂ s₁ s₂ hdecomposition hnorm₁ hnorm₂

end Pieces

/-- **The multiple-edge pocket region, uniformly in the parameters** (lane `kh-ejz`), with the
quantifier prefix of `OsinMultipleEdgeCutSectionStatement`. -/
def OsinMultipleEdgePocketRegionSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgePocketRegionInput.{u, w, v} D lambda c eps W

/-- **G2, multiple edges, uniformly in the parameters, from the pocket pieces.**  The thresholds
are those of the pocket region producer. -/
theorem osinMultipleEdgeCutSection_of_pieces
    (hpocket : OsinMultipleEdgePocketRegionSectionStatement.{u, w, v})
    (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v}) :
    OsinMultipleEdgeCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hpocket D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    multipleEdgeCutInput_of_pieces hcollar hcell hcondition hlambda1 hc
      (hrho rho hrho' W hcondition)⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ne_or_of_leastArea
#audit_axioms GroupApproximation.GGT.VanKampen.nonempty_osinMultipleEdgeCut_of_pocketRegion
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgeCutInput_of_pieces
#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgePocketRegionSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgeCutSection_of_pieces
