import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindNine
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'` on pockets of relator cells, and the `0`-cell residual

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-78.

`gfaceWindNine_Statement` is **FALSE** (lane gl-p10-73, scratchpad `gl-p10-73/leanexact.py`,
`nine_none.py`): in the pocket `K = {1,2,4}` of the map `sig = [6,14,0,19,9,4,18,1,5,7,12,2,13,
11,16,15,3,17,10,8]` (outer face `3`, walk `[1,10,6,5,19,2,9]`, relator cells `4` (kept) and `6`
(source)) the faces `1` and `2` of `K` are `0`-cells, i.e. faces of `K.faces` that are not relator
cells (`DiscDiagram.inner_face` allows them; `PocketFaceSet` does not forbid them), and no
arc-keeping winding state exists.

## Does `X.LeastArea` force the faces of `K` to be relator cells?  NO.

`DiscDiagram.LeastArea` bounds `rCellCount = relatorCells.length` only, so `0`-cells are free.
**LOUD: the counterexample above IS least area with letter labels** (scratchpad
`gl-p10-78/leastarea.py`): over `G = ℤ` with `D.base = univ`, dart values
`[0,0,0,0,-2,2,0,0,1,-1,-1,1,0,0,0,0,0,0,-1,1]` give face values `[0,0,0,-2,1,0,1,0]`, the
relator cells `4, 6` have value `1`, the other inner faces value `0`, and the boundary value is
`2`; a product of `m` conjugates of `±1` has absolute value `≤ m`, hence `rCellCount = 2 ≤ m`.
So `gfaceWindCell_rcell_of_leastArea` is FALSE, and `gfaceWindNine_Statement` stays FALSE under
least area and letter labels.  **LOUD: the `0`-cells cannot be removed there by surgery**:
`Surgery.GFaceMerge` merges two distinct adjacent `G`-faces, but faces `1 = [1,6]` and
`2 = [2,19,10]` of `K` are not adjacent to each other, and merging either with face `0` or `5`
(off `K`) changes the pocket.

## Route

* `gfaceWindCell_RCells K` (definition): every face of `K.faces` is a relator cell.
  `gfaceWindCell_zeroCell` (proved): otherwise `K.faces` has a `0`-cell, a face of value `1`
  (`DiscDiagram.inner_face`).  `gfaceWindCell_c5` (proved): under `gfaceWindCell_RCells K` clause
  5 of `gfaceWindNine_Arcs` holds as soon as the walk `c` meets the boundary cycle of `K`.
* `gfaceWindCell_NineStatement` (OPEN): `gfaceWindNine_Statement` with the extra hypothesis
  `gfaceWindCell_RCells K`.  `gfaceWindCell_nine_of_nine` (proved).  **Strictly weaker** than
  `gfaceWindNine_Statement`, which is false while this one has no known counterexample.
* `gfaceWindCell_CollapseStatement` (OPEN): `extremalGFaceProve_Statement` restricted to
  no-loop pockets with a `0`-cell (`¬ gfaceWindCell_RCells K`).
  `gfaceWindCell_collapse_of_extremal` (proved): **strictly weaker** than
  `extremalGFaceProve_Statement` (a strictly smaller domain; no converse is proved without the
  cell statement).  **LOUD: it is a domain restriction, not a surgery statement**, since no
  `0`-cell removal keeping `X` and `K` exists in the counterexample (see above).
* `gfaceWindCell_extremal_of_cell` (proved): the two statements give
  `extremalGFaceProve_Statement` (loop case `gfaceChoose_of_loop`, `r`-cell case through
  `gfaceWindNine_choice_of_arcs`, `0`-cell case the collapse statement).

## Truth check

Scratchpad `gl-p10-78/cellcheck.py` (Lean-exact model of `gl-p10-73/leanexact.py`, extremal
clauses computed literally by `extcx.py`, brute force over all `F'`).
* Counterexample above: the extremal clauses hold with `F' = {4}` or `{1,4}`
  (relator cells `{4,6}`), so the collapse statement holds there.
* See the lane report for the random and witness seed counts (r-cells `K.faces ∪ {source}` for
  the cell statement; r-cells `{kept, source}` with a `0`-cell in `K` for the collapse
  statement).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Cell

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket of relator cells**: every face of `K.faces` is the face of a relator cell. -/
def gfaceWindCell_RCells (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ f ∈ K.faces, ∃ i : Fin X.rCellCount, (cell X i).face = f

/-- **A `0`-cell in a pocket**: when not every face of `K.faces` is a relator cell, some face
of `K.faces` is not a relator cell and reads a word of value `1` (`DiscDiagram.inner_face`). -/
theorem gfaceWindCell_zeroCell (K : PocketFaceSet D eps X lo hi)
    (h : ¬ gfaceWindCell_RCells K) :
    ∃ f ∈ K.faces, (¬ ∃ i : Fin X.rCellCount, (cell X i).face = f) ∧
      GGT.RelLetter.listVal ((X.faceBoundary f).darts.map X.label) = 1 := by
  unfold gfaceWindCell_RCells at h
  have hex : ∃ f ∈ K.faces, ¬ ∃ i : Fin X.rCellCount, (cell X i).face = f := by
    by_contra hc
    exact h fun f hf => by
      by_contra hn
      exact hc ⟨f, hf, hn⟩
  obtain ⟨f, hf, hno⟩ := hex
  refine ⟨f, hf, hno, ?_⟩
  have hfo : f ≠ X.outerFace := fun he => K.outerFace_not_mem (by rw [← he]; exact hf)
  rcases X.inner_face f hfo with ⟨C, hC, hCf⟩ | h1
  · obtain ⟨n, hn⟩ := List.mem_iff_get.mp hC
    exact (hno ⟨n, show (X.relatorCells.get n).face = f by rw [hn]; exact hCf⟩).elim
  · exact h1

/-- **Clause 5 on a pocket of relator cells**: when every face of `K.faces` is a relator cell,
clause 5 holds at any walk `c` containing a dart of the boundary cycle of `K`. -/
theorem gfaceWindCell_c5 (K : PocketFaceSet D eps X lo hi) (hR : gfaceWindCell_RCells K)
    {c : List X.toCombMap.Dart} (g : X.toCombMap.Face → ℤ) {x : X.toCombMap.Dart}
    (hx : x ∈ c) (hxK : x ∈ K.boundary.cycle) : gfaceWindNine_C5 K c g := by
  obtain ⟨i, hif⟩ := hR _ ((K.boundary.cycle_mem_iff x).mp hxK).1
  unfold gfaceWindNine_C5
  exact Or.inl ⟨x, hx, i, Eq.subst (motive := fun y =>
    Relation.ReflTransGen (gfaceWindClause_Adj X.toCombMap c) (X.toCombMap.faceOf x) y)
    hif.symm Relation.ReflTransGen.refl⟩

/-- **The extremal clauses from an arc-keeping winding choice** (the chain
`gfaceWindNine_choice_of_arcs`, `gfaceWindSix_choice`, `gfaceWindClause_choice`,
`gfaceWind_of_choice`). -/
theorem gfaceWindCell_clauses_of_arcs (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWindNine_Arcs K) :
    ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F' :=
  gfaceWind_of_choice K hK (gfaceWindClause_choice K hK
    (gfaceWindSix_choice K hK (gfaceWindNine_choice_of_arcs K hK h)))

end Cell

/-- **The arc-keeping winding statement on pockets of relator cells** (OPEN; STRICTLY WEAKER than
the false `gfaceWindNine_Statement`, see the module docstring).  Under the premises of
`gfaceWindNine_Statement` and when every face of `K.faces` is a relator cell, an arc-keeping
winding choice exists. -/
def gfaceWindCell_NineStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
      gfaceWindCell_RCells K → gfaceWindNine_Arcs K

/-- **The cell statement from the arc-keeping winding statement** (drop the extra
hypothesis). -/
theorem gfaceWindCell_nine_of_nine (h : gfaceWindNine_Statement.{u, w, v}) :
    gfaceWindCell_NineStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL

/-- **The `0`-cell residual** (OPEN; STRICTLY WEAKER than `extremalGFaceProve_Statement`, a
domain restriction, see the module docstring).  Under the premises of
`extremalGFaceProve_Statement`, when no loop choice exists and some face of `K.faces` is not a
relator cell, some face set `F'` satisfies `extremalGFaceProve_Clauses`. -/
def gfaceWindCell_CollapseStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
      ¬ gfaceWindCell_RCells K →
        ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F'

/-- **The `0`-cell residual from the face-set flip statement** (drop two hypotheses). -/
theorem gfaceWindCell_collapse_of_extremal (h : extremalGFaceProve_Statement.{u, w, v}) :
    gfaceWindCell_CollapseStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose _ _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose

/-- **The face-set flip statement from the cell statement and the `0`-cell residual**: the
loop case by `gfaceChoose_of_loop`, a pocket of relator cells by the cell statement and
`gfaceWindCell_clauses_of_arcs`, a pocket with a `0`-cell by the residual. -/
theorem gfaceWindCell_extremal_of_cell (h : gfaceWindCell_NineStatement.{u, w, v})
    (hC : gfaceWindCell_CollapseStatement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  rcases Classical.em (gfaceChoose_Loop K) with hL | hL
  · exact gfaceChoose_of_loop K hK hpinch hL
  · rcases Classical.em (gfaceWindCell_RCells K) with hR | hR
    · exact gfaceWindCell_clauses_of_arcs K hK
        (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR)
    · exact hC D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_RCells
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_zeroCell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_c5
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_clauses_of_arcs
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_NineStatement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_nine_of_nine
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_CollapseStatement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_collapse_of_extremal
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCell_extremal_of_cell
