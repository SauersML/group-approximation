import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Def
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, Route B: lake-free noncrossing cell pockets are refuted below the bound

Lane gl-p06-07 of `carto-gl-p06`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

## The corrected statement

`CellPocketFaceSetLakeFreeEnclosedStatement` is the face-set form of
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`InnerTwoArcLong.lean:55`).  Its hypotheses
are a cell pocket face set `K` (`∂K = s_1 t̄_1 s_2 t̄_2`) with `i ≠ j`, letter labels, relator words
longer than one letter, a noncrossing boundary cycle, lake freeness
(`P06LakeFree.CellPocketLakeFree`, lane gl-p06-05) and a relator cell in `K.faces`.  Its conclusion
is copied verbatim from `InnerPocketEnclosedTwoArcStatement` (lines 74–81): an enclosed face set
turning to its successors, holding a relator cell, whose inverse outside walk reads
`s_1' Ā_1 s_2' Ā_2` with cells outside, `|s_1'|, |s_2'| ≤ ε` and `A_1` empty or `A_2` nonempty.

## Truth check (on paper)

* **The naive witness `faces = K.faces` can fail.**  Three petals `P_1, P_2, P_3` of `K` at one
  vertex `v`, in this rotation order, with `∂K` read in the order `P_1 P_3 P_2`:
  `P_1 = s_1^a`, `P_3 = s_1^b t̄_1 s_2^a`, `P_2 = s_2^b t̄_2`.  The successor order is
  `P_1 P_2 P_3`, cyclically `s_2^a s_1^a s_2^b t̄_2 s_1^b t̄_1`, whose first side chunk has length up
  to `2ε`.  So the order of `∂K` is not the successor order at pinches.  (Noncrossing in this corpus,
  `IsNoncrossingClosedWalk`, is a property of the dart set and does not fix this order.)
* **The edge class of the kept cell works.**  Let `P` be the edge class of a relator cell inside
  `K.faces`, with its lakes filled.  Every boundary dart of `P` faces a face off `K.faces` (a face of
  `K.faces` across an edge would lie in the class), so `∂P ⊆ ∂K`, and `Π_i`, `Π_j` stay outside.
  Lake freeness makes the petals of `K` meet like a cactus: two petals touching at two vertices
  would enclose a lake of `K`.  So `P` has a simple outside walk, and `∂K` restricted to `P` is read in
  the cyclic order of `∂P`.  A piece of `t̄_1` can leave `P` only around a loop of `∂Π_i` at a
  vertex, and inside such a loop every face is in `K` (else a lake of `K`); adding those petals
  makes the piece contiguous.  In the model above, the petal holding the cell reads `s_1^a` (both
  arcs empty), `s_2^b t̄_2`, or `s_2^a ∅ s_1^b t̄_1` with an empty first arc.
* Verdict: TRUE; lane gl-p06-08 closes it.  Without lake freeness it fails (case (d) of
  `Piece06.CellRoseLakesSurgeryBelowStatement`: every relator cell in `F'`).

## What this module proves

`false_of_lakeFree_below`: at `2 ≤ ρ` and `λ⁻¹ (3ε + c) < (μ/2) ρ`, below the inductive bound, a
lake-free noncrossing cell pocket face set does not exist.  The kept cell is `K.kept`.  The route
is `P07LakeExclusion.lakeFillTwoArcExit_of_enclosed` (`InnerTwoArcLongUnpinch.lean:148`), then
`Piece06.false_of_lakeFillTwoArcExit` (`LakesSurgery.lean:107`).  The length hypothesis is
`one_lt_length_of_two_le_rho`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **A lake-free noncrossing cell pocket face set encloses a two-arc pocket.**  A cell pocket face
set `K` between `Π_i ≠ Π_j`, with letter labels, relator words longer than one letter, a noncrossing
boundary cycle, no lakes and a relator cell inside, gives an enclosed face set of `X` that turns to
its successors, holds a relator cell, and whose inverse outside walk reads `s_1 Ā_1 s_2 Ā_2`, with
arcs of cells outside, `|s_1|, |s_2| ≤ ε`, and `A_1` empty or `A_2` nonempty.  The conclusion is
that of `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`.
* **Why it is true.**  Take the edge class of the relator cell, the petals of `K` inside loops of
  `∂Π_i`, `∂Π_j` at its vertices, and fill lakes.  Its boundary is a sub-walk of `∂K`, read in cyclic
  order, and merges into at most two sides and two arcs.  See the module docstring.
* **Why it is not the circular residual.**  The hypothesis `CellPocketLakeFree K` excludes case (d)
  of `Piece06.CellRoseLakesSurgeryBelowStatement`, and no O-equivalent copy is asked for. -/
def CellPocketFaceSetLakeFreeEnclosedStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j),
    i ≠ j →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle →
    CellPocketLakeFree K →
    ∀ C ∈ X.relatorCells, C.face ∈ K.faces →
      ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
        (k₁ k₂ : Fin X.rCellCount) (A₁ : CyclicArc (cellDarts X k₁))
        (A₂ : CyclicArc (cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
        EnclosedFaceSetSucc X faces outerWalk ∧
          (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
          (cell X k₁).face ∉ faces ∧ (cell X k₂).face ∉ faces ∧
          invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts ∧
          s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length)

section Refuted

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Lake-free noncrossing cell pockets are refuted below the bound.**  At `2 ≤ ρ` and
`λ⁻¹ (3ε + c) < (μ/2) ρ`, in a least-area diagram with letter labels where clause (b) of Lemma 9.7
holds below its number of relator cells, no cell pocket face set between distinct cells has a
noncrossing boundary cycle and no lakes.  The enclosed statement at the kept cell `K.kept` gives a
two-arc lake exit (`lakeFillTwoArcExit_of_enclosed`), and clause (b) refutes it
(`Piece06.false_of_lakeFillTwoArcExit`). -/
theorem false_of_lakeFree_below (h : CellPocketFaceSetLakeFreeEnclosedStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j) (hij : i ≠ j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle) (hfree : CellPocketLakeFree K) :
    False := by
  have hW : ∀ word ∈ W, 1 < word.length := one_lt_length_of_two_le_rho hcondition hrho
  obtain ⟨faces, outerWalk, k₁, k₂, A₁, A₂, s₁, s₂, E, ⟨C', hC', hCf'⟩, hk₁, hk₂, hdec, hs₁, hs₂,
      hpos⟩ :=
    h D eps X K hij hlabel hW hw hfree (cell X K.kept) (cell_mem X K.kept) K.kept_mem
  exact Piece06.false_of_lakeFillTwoArcExit hcondition hlambda hlambda1 hc hmu hmu1 hrho hlarge
    hlea hbelow
    (P07LakeExclusion.lakeFillTwoArcExit_of_enclosed hW hlabel E hC' hCf' hk₁ hk₂ A₁ A₂ hdec hs₁
      hs₂ hpos)

end Refuted

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketFaceSetLakeFreeEnclosedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.false_of_lakeFree_below
