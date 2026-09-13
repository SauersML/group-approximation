import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellSameCell
import GroupApproximation.Meta.AxiomGuard

/-!
# The loop cut from a pocket region meeting its cell along two arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "it is easy to show that `Φ_M` can not
contain loops either.  The only difference is that the subdiagram `Ξ` will be bounded by `st`,
where `l(s) < ε` and `t` is a subpath of `∂Π_1`."  In the cell-pinch branch of Lemma 9.4, Case 1,
excising an innermost lobe of value one from a pinched walk along `∂Π` leaves a pocket whose inverse
complement cycle reads a side `s` and then TWO arcs of the same cell `i`, read backwards.

The multiple-edge cut (`nonempty_osinMultipleEdgeCut_of_pocketRegion`) already allows its two
arcs to belong to one cell: neither it nor `PocketRegion.fourSectionCuts_cellTransport` asks
`i ≠ j`, because a region to either arc glues back into a region from the kept cell to `i`.  With
an empty second side, a two-arc pocket is a multiple-edge cut, and
`OsinMultipleEdgeCut.false_of_below` refutes it below the number of relator cells of `Δ`.

* `nonempty_osinLoopCut_of_pocketRegion_twoArcs`: the cut, at `j = i` and `s₂ = []`.
* `false_of_pocketRegion_of_below_twoArcs`: the refutation, with the hypotheses of
  `false_of_pocketRegion_of_below` and two arcs of `i`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.4, Case 1, and Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

section TwoArcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The cut from a pocket region meeting a cell along two arcs.**  Take a pocket region of an
O-equivalent copy `X` of a least-area `Δ`, with legal labels, both cycles following the boundary,
a relator cell inside and a cell `i` outside.  Let its inverse complement cycle read a side `s` of
value of word norm at most `ε`, then two arcs of `i` read backwards.  Under `C(ε, μ, λ, c, ρ)`
with `λ ≤ 1` and `0 ≤ c`, it is a multiple-edge cut of `Δ` with the second side empty. -/
theorem nonempty_osinLoopCut_of_pocketRegion_twoArcs
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
    (A₁ A₂ : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle = s ++ invDarts X A₁.darts ++ invDarts X A₂.darts)
    (hnorm : wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps) :
    Nonempty (OsinMultipleEdgeCut D lambda c eps Delta) := by
  have hdecomposition' : invDarts X P.outer.cycle =
      s ++ invDarts X A₁.darts ++ ([] : List X.toCombMap.Dart) ++ invDarts X A₂.darts := by
    rw [hdecomposition, List.append_nil]
  have hnorm₂ : wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord X ([] : List X.toCombMap.Dart))) ≤ eps := by
    simp only [dartWord, List.map_nil, RelLetter.listVal_nil, wordNorm_one]
    exact Nat.zero_le _
  exact nonempty_osinMultipleEdgeCut_of_pocketRegion hcollar hcell hcondition hlambda hc hlea
    equiv hlabel P hin hout hC hCf hi hi A₁ A₂ s [] hdecomposition' hnorm hnorm₂

end TwoArcs

/-- **A pocket meeting a cell along two arcs, refuted below `Δ`.**  The hypotheses of
`false_of_pocketRegion_of_below`, with the inverse complement cycle reading a side `s` and then two
arcs of `i` backwards.  The multiple-edge cut with an empty second side and clause (b) of Lemma 9.7
below the number of relator cells of `Δ` give a contradiction
(`OsinMultipleEdgeCut.false_of_below`). -/
theorem false_of_pocketRegion_of_below_twoArcs (hcollar : GeodesicCollarStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {Delta X : DiscDiagram.{u, w, v} W} (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    (equiv : OEquivalentDiscDiagram Delta X)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (P : PocketRegion X) (hin : P.inner.FollowsBoundary) (hout : P.outer.FollowsBoundary)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ P.faces) {i : Fin X.rCellCount} (hi : (cell X i).face ∉ P.faces)
    (A₁ A₂ : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle = s ++ invDarts X A₁.darts ++ invDarts X A₂.darts)
    (hnorm : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps) :
    False := by
  obtain ⟨cut⟩ := nonempty_osinLoopCut_of_pocketRegion_twoArcs hcollar pocketCellTransport
    hW hlambda1 hc hleast equiv hlabel P hin hout hC hCf hi A₁ A₂ s hdecomposition hnorm
  exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 hrho hlarge hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.nonempty_osinLoopCut_of_pocketRegion_twoArcs
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_pocketRegion_of_below_twoArcs
