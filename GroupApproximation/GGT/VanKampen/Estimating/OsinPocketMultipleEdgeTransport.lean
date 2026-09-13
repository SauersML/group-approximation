import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell transports of the multiple-edge pocket cut

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a).  Two distinct contiguity regions between the
same two cells `i` and `j` cut out a pocket `Ξ` with `∂Ξ = s_1 t_1 s_2 t_2`, where `t_1` and `t_2`
are arcs of the two cells read backwards.  The pocket is a least-area cut with four sections
(`PocketRegion.fourSectionCuts`).  A region of an O-equivalent copy of the pocket to section `1`
or `3`, the arc of `i` or of `j`, glues back into a region of an O-equivalent copy of `X` from a
cell to another cell, with the same contiguity degree.

* `PocketRegion.fourSectionCuts_cellTransport`: both transports, from
  `PocketCellTransportStatement` (lane `go-lemma42`) at `pre = s_1` and at
  `pre = s_1 t_1 s_2`.  This is the `htransport` argument of the multiple-edge cut assembly of
  lane `hull-select`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

section

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

private theorem partsCut_map_label {α β : Type*} (f : α → β) (parts : List (List α)) (k : ℕ) :
    CutSections.partsCut (parts.map (List.map f)) k = CutSections.partsCut parts k := by
  unfold CutSections.partsCut
  rw [← List.map_take, ← List.map_flatten, List.length_map]

private theorem partsCut_four_first {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 1 = a.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_second {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (1 + 1) = a.length + b.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_third {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 3 = a.length + b.length + c.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

private theorem partsCut_four_fourth {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (3 + 1) =
      a.length + b.length + c.length + d.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

namespace PocketRegion

/-- **The cell transports of the multiple-edge pocket cut.**  Let the inverse complement cycle of
a pocket region of `X` split as `s_1 t_1 s_2 t_2`, with `t_1` and `t_2` arcs of the cells `i` and
`j` outside the pocket read backwards, and all four parts quasi-geodesic.  A region of an
O-equivalent copy of the pocket to section `1` or `3` of the four sections glues back into a region
of an O-equivalent copy of `X` from a cell to another cell, with the same contiguity degree. -/
theorem fourSectionCuts_cellTransport (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (P : PocketRegion X) (hout : P.outer.FollowsBoundary)
    {i j : Fin X.rCellCount} (hi : (cell X i).face ∉ P.faces) (hj : (cell X j).face ∉ P.faces)
    (A₁ : CyclicArc (cellDarts X i)) (A₂ : CyclicArc (cellDarts X j))
    (s₁ s₂ : List X.toCombMap.Dart)
    (hdecomposition : invDarts X P.outer.cycle =
      s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hquasi : ∀ part ∈ [s₁, invDarts X A₁.darts, s₂, invDarts X A₂.darts],
      IsLambdaCQuasiGeodesicWord D lambda c (dartWord X part)) :
    ∀ k : Fin (P.fourSectionCuts D lambda c s₁ (invDarts X A₁.darts) s₂
        (invDarts X A₂.darts) hdecomposition hquasi).count,
      ((k : ℕ) = 1 ∨ (k : ℕ) = 3) →
        ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram P.diagram Xi →
          ∀ a : RegionCandidate D eps Xi,
            RegionCandidate.TargetsSectionIndex (P.fourSectionCuts D lambda c s₁
                (invDarts X A₁.darts) s₂ (invDarts X A₂.darts) hdecomposition hquasi) k a →
              ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                (t : Fin Y.rCellCount),
                Nonempty (OEquivalentDiscDiagram X Y) ∧ b.2.target = some t ∧
                  b.2.source ≠ t ∧ b.contiguityDegree = a.contiguityDegree := by
  have hcut : ∀ k : Fin ((P.fourSectionCuts D lambda c s₁ (invDarts X A₁.darts) s₂
      (invDarts X A₂.darts) hdecomposition hquasi).count + 1),
      (P.fourSectionCuts D lambda c s₁ (invDarts X A₁.darts) s₂ (invDarts X A₂.darts)
          hdecomposition hquasi).cut k =
        CutSections.partsCut [s₁, invDarts X A₁.darts, s₂, invDarts X A₂.darts] k :=
    fun k => partsCut_map_label X.label [s₁, invDarts X A₁.darts, s₂, invDarts X A₂.darts] k
  have hinv₁ : (invDarts X A₁.darts).length = A₁.length := by
    rw [invDarts, List.length_map, List.length_reverse, CyclicArc.darts_length]
  have hinv₂ : (invDarts X A₂.darts).length = A₂.length := by
    rw [invDarts, List.length_map, List.length_reverse, CyclicArc.darts_length]
  intro k hk Xi E a ha
  obtain ⟨hnone, hlo, hhi⟩ := ha
  rcases hk with hk | hk
  · rw [hcut, Fin.val_castSucc, hk, partsCut_four_first] at hlo
    rw [hcut, Fin.val_succ, hk, partsCut_four_second, hinv₁] at hhi
    exact hcell D eps W X P hout i hi A₁ s₁ (s₂ ++ invDarts X A₂.darts)
      (by simp only [hdecomposition, List.append_assoc]) Xi E a hnone hlo hhi
  · rw [hcut, Fin.val_castSucc, hk, partsCut_four_third] at hlo
    rw [hcut, Fin.val_succ, hk, partsCut_four_fourth, hinv₂] at hhi
    exact hcell D eps W X P hout j hj A₂ (s₁ ++ invDarts X A₁.darts ++ s₂) []
      (by simp only [hdecomposition, List.append_nil]) Xi E a hnone
      (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)

end PocketRegion

end

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.fourSectionCuts_cellTransport
