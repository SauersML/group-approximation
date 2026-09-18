import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedLoopPocketUnpinch
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellGoodCorners
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCutSuccProof
import GroupApproximation.Manuscript.NonMF.Full.GL06g.Exit
import GroupApproximation.Manuscript.NonMF.Full.GL06g.Doubling
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e: an enclosed face set with two arcs outside unpinches to a two-arc exit

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

An enclosed face set `faces` of `X` with successor turns, holding a relator cell, with two cells
`Π_{k_1}`, `Π_{k_2}` off it, whose inverse outer walk reads `s_1 A_1⁻¹ s_2 A_2⁻¹` with sides of
length at most `ε`, gives a pocket region of an O-equivalent copy with the same shape
(`GL06g.TwoArcExit`).

* `twoArcExit_of_bridgeFree`: both arcs nonempty and the walk bridge-free.  The face set is a
  cell pocket face set (`CellPocketFaceSet.ofBoundaryCycle`) in first-turn order, and
  `CellPocketFaceSet.copyRegion_of_firstTurns` gives the region.
* `twoArcExit_of_emptyFirstArc`: the first arc is empty.  The walk reads `(s_1 s_2) A_2⁻¹`, the
  one-arc pocket region `enclosedLoopPocketRegionSucc_of_pieces` keeps the side word, and the side
  is split back at `|s_1|`, with an empty first arc.
* `twoArcExit_of_enclosed`: the general case, doubling the bridges first
  (`GL06g.exists_bridgeFree_of_enclosed`) and transporting the exit back
  (`GL06g.TwoArcExit.of_oEquivalent`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06e

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

section TwoArc

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The empty arc at position `0` of a cycle. -/
def emptyArc {α : Type*} (cycle : List α) : CyclicArc cycle :=
  ⟨⟨0, Nat.succ_pos _⟩, 0, Nat.zero_le _⟩

/-- The empty arc has no darts. -/
theorem emptyArc_darts {α : Type*} (cycle : List α) : (emptyArc cycle).darts = [] := rfl

/-- The inverse of the empty dart list is empty. -/
theorem invDarts_empty (Y : DiscDiagram.{u, w, v} W) :
    invDarts Y ([] : List Y.toCombMap.Dart) = [] := rfl

/-- **A bridge-free enclosed face set with two nonempty arcs outside gives a two-arc exit**
(Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The face set with its
boundary cycle is a cell pocket face set in first-turn order, which unpinches to a pocket region
of an O-equivalent copy. -/
theorem twoArcExit_of_bridgeFree (D : RelGenSet G Lambda) {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hW : ∀ word ∈ W, 1 < word.length)
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk)
    (hC : ∃ C ∈ X.relatorCells, C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    (s₁ s₂ : List X.toCombMap.Dart)
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (hpos₁ : 0 < A₁.length) (hpos₂ : 0 < A₂.length) : GL06g.TwoArcExit D eps X := by
  obtain ⟨C, hCmem, hCf⟩ := hC
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hCmem
  have hn₁ := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁
  have hn₂ := (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂
  let K : CellPocketFaceSet D eps X k₁ k₂ :=
    CellPocketFaceSet.ofBoundaryCycle (EnclosedLoopPocket.enclosedBoundaryCycle E hfree)
      ⟨k, hk⟩ A₁ A₂ s₁ s₂ hdec E.outerFace_not_mem hpos₁ hpos₂ hCf hs₁ hs₂ hn₁ hn₂
  have hK₀ := EnclosedLoopPocket.pocketFaceSet_firstTurns D E hfree ⟨k, hk⟩ hCf k₂ hk₂ A₂
    (s₁ ++ invDarts X A₁.darts ++ s₂) hdec
  have hK : K.FirstTurns := hK₀
  obtain ⟨X', hE, hlabel', P, C', i', j', s₁', s₂', A₁', A₂', hC', hCf', hi', hj', hdec', hn₁',
    hn₂', hin, hout⟩ := K.copyRegion_of_firstTurns hW hlabel hK
  exact ⟨X', P, C', i', j', A₁', A₂', s₁', s₂', hE, hlabel', hin, hout, hC', hCf', hi', hj', hdec',
    hn₁', hn₂'⟩

/-- **An enclosed face set whose first arc is empty gives a two-arc exit** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The walk reads `(s_1 s_2) A_2⁻¹`; the
one-arc pocket region keeps the side word, which is split back at `|s_1|`. -/
theorem twoArcExit_of_emptyFirstArc (D : RelGenSet G Lambda) {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hW : ∀ word ∈ W, 1 < word.length)
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    (hC : ∃ C ∈ X.relatorCells, C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    (s₁ s₂ : List X.toCombMap.Dart)
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (h0 : A₁.length = 0) : GL06g.TwoArcExit D eps X := by
  obtain ⟨C, hCmem, hCf⟩ := hC
  have hA₁ : A₁.darts = [] := List.eq_nil_of_length_eq_zero (A₁.darts_length.trans h0)
  have hdec₁ : invDarts X outerWalk = (s₁ ++ s₂) ++ invDarts X A₂.darts := by
    rw [hdec, hA₁, invDarts_empty, List.append_nil]
  obtain ⟨X', P, C', i', A', s', hE, hlabel', hin, hout, hC', hCf', hi', hdec', hword'⟩ :=
    enclosedLoopPocketRegionSucc_of_pieces.{u, w, v} enclosedBridgeDoublingSideArcSucc.{u, w, v}
      enclosedLoopPocketUnpinchSucc.{u, w, v} D hW X hlabel faces outerWalk E C hCmem hCf k₂ hk₂
      A₂ (s₁ ++ s₂) hdec₁
  have hw₁ : dartWord X' (s'.take s₁.length) = dartWord X s₁ := by
    have e1 : dartWord X' (s'.take s₁.length) = (dartWord X' s').take s₁.length := by
      show (s'.take s₁.length).map X'.label = (s'.map X'.label).take s₁.length
      exact List.map_take
    have e2 : (dartWord X (s₁ ++ s₂)).take s₁.length = dartWord X s₁ := by
      show ((s₁ ++ s₂).map X.label).take s₁.length = s₁.map X.label
      rw [List.map_append, List.take_left' (List.length_map _)]
    rw [e1, hword', e2]
  have hw₂ : dartWord X' (s'.drop s₁.length) = dartWord X s₂ := by
    have e1 : dartWord X' (s'.drop s₁.length) = (dartWord X' s').drop s₁.length := by
      show (s'.drop s₁.length).map X'.label = (s'.map X'.label).drop s₁.length
      exact List.map_drop
    have e2 : (dartWord X (s₁ ++ s₂)).drop s₁.length = dartWord X s₂ := by
      show ((s₁ ++ s₂).map X.label).drop s₁.length = s₂.map X.label
      rw [List.map_append, List.drop_left' (List.length_map _)]
    rw [e1, hword', e2]
  refine ⟨X', P, C', i', i', emptyArc (cellDarts X' i'), A', s'.take s₁.length,
    s'.drop s₁.length, hE, hlabel', hin, hout, hC', hCf', hi', hi', ?_, ?_, ?_⟩
  · rw [hdec', emptyArc_darts, invDarts_empty, List.append_nil, List.take_append_drop]
  · rw [hw₁]
    exact (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁
  · rw [hw₂]
    exact (PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂

/-- **An enclosed face set with two arcs outside gives a two-arc exit** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  An empty first arc is handled directly;
otherwise both arcs are nonempty, the bridges are doubled in an O-equivalent copy keeping the arc
lengths and the side lengths, the bridge-free face set unpinches, and the exit transports back. -/
theorem twoArcExit_of_enclosed (D : RelGenSet G Lambda) {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hW : ∀ word ∈ W, 1 < word.length)
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    (hC : ∃ C ∈ X.relatorCells, C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₁ : (cell X k₁).face ∉ faces)
    (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    (s₁ s₂ : List X.toCombMap.Dart)
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (hpos : A₁.length = 0 ∨ 0 < A₂.length) : GL06g.TwoArcExit D eps X := by
  by_cases h0 : A₁.length = 0
  · exact twoArcExit_of_emptyFirstArc D hlabel hW E hC hk₂ A₁ A₂ s₁ s₂ hdec hs₁ hs₂ h0
  · have hpos₁ : 0 < A₁.length := Nat.pos_of_ne_zero h0
    have hpos₂ : 0 < A₂.length := hpos.resolve_left h0
    obtain ⟨X₁, faces₁, outerWalk₁, k₁', k₂', A₁', A₂', s₁', s₂', hE, hlabel₁, E₁, hfree₁, hC₁, -,
      hk₂', hdec₁, hA₁, hA₂, hl₁, hl₂, -, -⟩ :=
      GL06g.exists_bridgeFree_of_enclosed D hlabel E hC hk₁ hk₂ A₁ A₂ s₁ s₂ hdec
    have hs₁' : s₁'.length ≤ eps := (le_of_eq hl₁).trans hs₁
    have hs₂' : s₂'.length ≤ eps := (le_of_eq hl₂).trans hs₂
    have hpos₁' : 0 < A₁'.length := lt_of_lt_of_eq hpos₁ hA₁.symm
    have hpos₂' : 0 < A₂'.length := lt_of_lt_of_eq hpos₂ hA₂.symm
    exact GL06g.TwoArcExit.of_oEquivalent hE
      (twoArcExit_of_bridgeFree D hlabel₁ hW E₁ hfree₁ hC₁ hk₂' A₁' A₂' s₁' s₂' hdec₁ hs₁' hs₂'
        hpos₁' hpos₂')

end TwoArc

end GroupApproximation.Full.GL06e

#audit_axioms GroupApproximation.Full.GL06e.emptyArc
#audit_axioms GroupApproximation.Full.GL06e.emptyArc_darts
#audit_axioms GroupApproximation.Full.GL06e.invDarts_empty
#audit_axioms GroupApproximation.Full.GL06e.twoArcExit_of_bridgeFree
#audit_axioms GroupApproximation.Full.GL06e.twoArcExit_of_emptyFirstArc
#audit_axioms GroupApproximation.Full.GL06e.twoArcExit_of_enclosed
