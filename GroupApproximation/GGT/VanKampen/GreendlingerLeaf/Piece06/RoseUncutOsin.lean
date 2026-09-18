import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseUncut
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the uncut rose under Osin's condition, the perimeter of a side cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`, where
`|s_1|, |s_2| ≤ ε` and the relators have length at least `ρ ≫ ε`.

`CellRoseUncutOsinStatement` (module `Piece06/RoseUncut`) is the uncut rose step under the
binders of `CellPocketOuterPinchStepSectionDistinctStatement`.  This module formalizes the part of
Osin's condition that excludes the three-petal configuration of that module's docstring, and
isolates what is left.

## The mathematics

Let `K` be a cell pocket face set with boundary cycle `s_1 t̄_1 s_2 t̄_2`.

1. **A side cell** (`SideCell K k`) is a relator cell `k` all of whose boundary darts
   (`cellDarts X k`) lie on the sides `s_1 ++ s_2`.  In the three-petal model the kept petal is the
   single cell `kept`: its edges have faces off `K` on their other sides, and the petal carries no
   arc, so `SideCell K kept`.
2. **The perimeter bound** (`length_cellDarts_le_of_sideCell`).  The boundary darts of a cell are
   pairwise distinct (`cellDarts_nodup`), so a side cell has at most `|s_1| + |s_2| ≤ 2ε` darts
   (a duplicate-free sublist of `s_1 ++ s_2` up to permutation, `List.subperm_of_subset`).
3. **Its word** (`length_word_le_of_sideCell`).  The word of the cell is read on its darts
   (`dartWord_cellDarts`), one letter per dart, so it has length at most `2ε`.
4. **Osin's condition** (`not_sideCell_of_osinCCondition`).  The word of a cell lies in `W`
   (`RelatorCell.word_mem`), and `OsinCCondition` gives `ρ ≤ |word|` (field `long` of
   `RelWord.IsSmallCancellation`).  So no side cell exists once `2ε < ρ`.
5. **The reduction** (`cellRoseUncutOsin_of_offSide`).  Keep the `ε₀` of the residual and raise the
   `ρ₀` to `max ρ₀ (2ε + 1)`.  Every uncut rose then has no side cell, and the residual
   `CellRoseUncutOffSideStatement` applies.  Conversely the residual follows from
   `CellRoseUncutOsinStatement` by forgetting the extra hypothesis (`cellRoseUncutOffSide_of_osin`),
   so the two are equivalent.
6. **Piece 06** (`proof_of_cellRoseUncutOffSide`): with `BadCornerRefinementStatement`, through
   `proof_of_cellRoseUncutOsin`.

## The remaining gap

`CellRoseUncutOffSideStatement` (OPEN): `CellRoseUncutOsinStatement` with the extra hypothesis that
no relator cell lies on the sides.  What it still has to handle:

* *Petals with several faces.*  The kept petal `P_k` may contain G-cells besides the relator cells.
  Its boundary still lies on the sides, so it is a subdiagram with boundary word of length at most
  `2ε` containing a relator cell.  Excluding it is Greendlinger's lemma for short boundaries (a
  least-area diagram over `W` with boundary length `≤ 2ε < ρ` holds no relator cell), which at this
  point of the induction is not available.
* *Lakes.*  Components of the complement of `K.faces` away from the exterior touching `∂K`; the
  filling surgery for cell pockets is not formalized (see `Piece06/RoseCut`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Perimeter

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A relator cell on the sides of a cell pocket**: every boundary dart of the cell lies on the
first or the second side of the boundary cycle. -/
def SideCell (K : CellPocketFaceSet D eps X i j) (k : Fin X.rCellCount) : Prop :=
  ∀ d ∈ cellDarts X k, d ∈ K.firstSide ++ K.secondSide

/-- **The perimeter of a side cell is at most `2ε`**: its darts are distinct and lie on the two
sides. -/
theorem length_cellDarts_le_of_sideCell {K : CellPocketFaceSet D eps X i j}
    {k : Fin X.rCellCount} (h : SideCell K k) : (cellDarts X k).length ≤ eps + eps := by
  have hsub : cellDarts X k ⊆ K.firstSide ++ K.secondSide := by
    intro d hd
    exact h d hd
  have hlen : (cellDarts X k).length ≤ (K.firstSide ++ K.secondSide).length :=
    (List.subperm_of_subset (cellDarts_nodup X k) hsub).length_le
  rw [List.length_append] at hlen
  exact hlen.trans (Nat.add_le_add K.firstSide_length_le K.secondSide_length_le)

/-- **The word of a side cell has length at most `2ε`**: it is read on the darts of the cell. -/
theorem length_word_le_of_sideCell {K : CellPocketFaceSet D eps X i j}
    {k : Fin X.rCellCount} (h : SideCell K k) : (cell X k).word.length ≤ eps + eps := by
  have hw : (cell X k).word.length = (cellDarts X k).length := by
    rw [← dartWord_cellDarts X k]
    exact List.length_map _
  rw [hw]
  exact length_cellDarts_le_of_sideCell h

/-- **Under Osin's condition with `2ε < ρ` no relator cell lies on the sides**: relator words have
length at least `ρ`. -/
theorem not_sideCell_of_osinCCondition {mu lambda c : ℝ} {rho : ℕ}
    (hcond : OsinCCondition D W eps mu lambda c rho) (hlt : eps + eps < rho)
    (K : CellPocketFaceSet D eps X i j) (k : Fin X.rCellCount) : ¬ SideCell K k := by
  intro h
  have hlong : rho ≤ (cell X k).word.length :=
    hcond.toIsSmallCancellation.long (cell X k).word (cell X k).word_mem
  have hshort := length_word_le_of_sideCell h
  omega

end Perimeter

/-- **The uncut rose step under Osin's condition, off the side cells** (OPEN; the residual of gap 6).
`CellRoseUncutOsinStatement` with the extra hypothesis that no relator cell lies on the sides of
`K`.  It is equivalent to `CellRoseUncutOsinStatement` (`cellRoseUncutOsin_of_offSide`,
`cellRoseUncutOffSide_of_osin`). -/
def CellRoseUncutOffSideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces → AllNonFirstTurnsCrossed K → ¬ CellCut K →
                  (∀ k : Fin X.rCellCount, ¬ SideCell K k) →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The uncut rose step under Osin's condition from its off-side residual**: raising `ρ₀` past
`2ε` excludes the side cells (`not_sideCell_of_osinCCondition`). -/
theorem cellRoseUncutOsin_of_offSide (h : CellRoseUncutOffSideStatement.{u, w, v}) :
    CellRoseUncutOsinStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨max rho0 (eps + eps + 1), lt_of_lt_of_le hrho0 (le_max_left _ _),
    fun rho hrho' W hcond X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hrose hcut => ?_⟩
  have hlt : eps + eps < rho := by
    have hmax := (le_max_right rho0 (eps + eps + 1)).trans hrho'
    omega
  exact hrho rho ((le_max_left _ _).trans hrho') W hcond X i j hij hlea hlabel K hK hnft hfirst
    hsecond hpinch hrose hcut (fun k => not_sideCell_of_osinCCondition hcond hlt K k)

/-- **The off-side residual from the uncut rose step under Osin's condition**: forget the extra
hypothesis.  So the residual is no stronger than `CellRoseUncutOsinStatement`. -/
theorem cellRoseUncutOffSide_of_osin (h : CellRoseUncutOsinStatement.{u, w, v}) :
    CellRoseUncutOffSideStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch
    hrose hcut _ => hrho rho hrho' W hcond X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch
      hrose hcut⟩

/-- **Piece 06 of the Greendlinger leaf from the off-side residual**: through
`cellRoseUncutOsin_of_offSide` and `proof_of_cellRoseUncutOsin`, with the corner doubling
`BadCornerRefinementStatement` (OPEN, gap 5). -/
theorem proof_of_cellRoseUncutOffSide (h : CellRoseUncutOffSideStatement.{u, w, v})
    (hcorner : BadCornerRefinementStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v} :=
  proof_of_cellRoseUncutOsin (cellRoseUncutOsin_of_offSide h) hcorner

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.SideCell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.length_cellDarts_le_of_sideCell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.length_word_le_of_sideCell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.not_sideCell_of_osinCCondition
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutOffSideStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseUncutOsin_of_offSide
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseUncutOffSide_of_osin
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.proof_of_cellRoseUncutOffSide
