import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWrapMonogon
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell pinch at `ε = 0`, on monogon cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

A model test for `CellPocketPinchPosStatement` (`Estimating/OsinPocketCellFaceSet.lean`), and the
reason for its binder `0 < eps`.  This is the cell-to-cell analogue of `PocketWrap`
(`Estimating/OsinPocketWrapMonogon.lean`), whose rose refuted `PocketPinchLabelledStatement` at
`ε = 0`.

* `CellPocketWrap.not_simple_of_monogon_cells`: a cell pocket face set at `ε = 0` whose two cells
  each have one dart is never simple.  Its sides are empty and each arc is the only dart of its
  cell, so the boundary cycle is `[alpha x, alpha y]`.  The dart `x` is a loop, so `alpha x` starts
  where `x` starts, and walk order makes that the start of `alpha y`.  The two darts of the cycle
  then start at one vertex.
* `CellPocketWrap.no_simple_of_oEquivalent_monogon_cells`: an O-equivalence keeps the lengths of
  the relator words, so no O-equivalent copy of a diagram on one-letter relator words has a simple
  cell pocket face set at `ε = 0`.
* `CellPocketWrap.pinchConclusion_fails_of_monogon_cells`: so at `ε = 0` on such a diagram the
  conclusion of the pinch fails for every cell pocket face set.

Calibration only: no diagram carrying a cell pocket face set in walk order on monogon cells is built
here, so nothing is refuted.  At `ε > 0` the sides can absorb darts and the argument does not
apply.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace CellPocketWrap

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {X : DiscDiagram.{u, w, v} W}

/-- **A cell pocket face set at `ε = 0` on monogon cells is not simple.** -/
theorem not_simple_of_monogon_cells {i j : Fin X.rCellCount} (K : CellPocketFaceSet D 0 X i j)
    (hi : (cellDarts X i).length = 1) (hj : (cellDarts X j).length = 1) : ¬ K.Simple := by
  intro hK
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hi
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hj
  have h1l : K.firstArc.darts.length ≤ 1 :=
    K.firstArc.darts_length.trans_le (K.firstArc.length_le.trans_eq hi)
  have h2l : K.secondArc.darts.length ≤ 1 :=
    K.secondArc.darts_length.trans_le (K.secondArc.length_le.trans_eq hj)
  have h1m : ∀ d ∈ K.firstArc.darts, d = x := fun d hd => by
    have h := K.firstArc.mem_cycle_of_mem_darts hd
    rw [hx, List.mem_singleton] at h
    exact h
  have h2m : ∀ d ∈ K.secondArc.darts, d = y := fun d hd => by
    have h := K.secondArc.mem_cycle_of_mem_darts hd
    rw [hy, List.mem_singleton] at h
    exact h
  have ht1 : K.firstArc.darts = [x] := by
    rcases PocketWrap.eq_nil_or_eq_singleton h1l h1m with h | h
    · have hpos := K.firstArc_pos
      rw [← K.firstArc.darts_length, h] at hpos
      exact absurd hpos (by simp)
    · exact h
  have ht2 : K.secondArc.darts = [y] := by
    rcases PocketWrap.eq_nil_or_eq_singleton h2l h2m with h | h
    · have hpos := K.secondArc_pos
      rw [← K.secondArc.darts_length, h] at hpos
      exact absurd hpos (by simp)
    · exact h
  have hdec := K.decomposition
  rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp K.firstSide_length_le),
    List.eq_nil_of_length_eq_zero (Nat.le_zero.mp K.secondSide_length_le)] at hdec
  have hC : K.boundary.cycle = [X.toCombMap.alpha x, X.toCombMap.alpha y] := by
    rw [hdec, ht1, ht2]
    rfl
  have h : IsSimpleClosedWalk X.toCombMap K.boundary.cycle := hK
  rw [hC] at h
  have hchain := List.isChain_pair.mp h.chain
  rw [X.toCombMap.alpha_involutive x] at hchain
  have hfx : X.toCombMap.sigma (X.toCombMap.alpha x) = x :=
    PocketWrap.facePerm_eq_self_of_darts_eq (X.faceBoundary (cell X i).face) hx
  have hvx : X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf x :=
    (X.toCombMap.vertexOf_sigma (X.toCombMap.alpha x)).symm.trans
      (congrArg X.toCombMap.vertexOf hfx)
  have hnd := h.vertex_nodup
  change [X.toCombMap.vertexOf (X.toCombMap.alpha x),
    X.toCombMap.vertexOf (X.toCombMap.alpha y)].Nodup at hnd
  exact (List.nodup_cons.mp hnd).1 (List.mem_singleton.mpr (hvx.trans hchain))

/-- **No O-equivalent copy of a diagram on one-letter relator words has a simple cell pocket face
set at `ε = 0`.** -/
theorem no_simple_of_oEquivalent_monogon_cells {X' : DiscDiagram.{u, w, v} W}
    (e : OEquivalentDiscDiagram X X') (hcells : ∀ k, (cell X k).word.length = 1)
    {i' j' : Fin X'.rCellCount} (K' : CellPocketFaceSet D 0 X' i' j') : ¬ K'.Simple := by
  have hlen : ∀ k' : Fin X'.rCellCount, (cellDarts X' k').length = 1 := by
    intro k'
    have h := e.cellWord_eq (e.cellIndex.symm k')
    rw [Equiv.apply_symm_apply] at h
    rw [PocketWrap.cellDarts_length_eq_word_length, h]
    exact hcells _
  exact not_simple_of_monogon_cells K' (hlen i') (hlen j')

/-- **The conclusion of the cell pinch fails at `ε = 0` on one-letter relator words.** -/
theorem pinchConclusion_fails_of_monogon_cells (hcells : ∀ k, (cell X k).word.length = 1) :
    ¬ ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D 0 X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple := by
  rintro ⟨X', i', j', K', ⟨e⟩, -, hsimple⟩
  exact no_simple_of_oEquivalent_monogon_cells e hcells K' hsimple

end CellPocketWrap

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWrap.not_simple_of_monogon_cells
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWrap.no_simple_of_oEquivalent_monogon_cells
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWrap.pinchConclusion_fails_of_monogon_cells
