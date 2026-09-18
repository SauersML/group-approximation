import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindCollapseCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The `0`-cell residual: the excision choice of `F'`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-83.

`gfaceWindCell_CollapseStatement` (`Piece10Live/GFaceWindCell`) asks for a face set `F'` with
`extremalGFaceProve_Clauses K F'` on no-loop pockets with a `0`-cell.  This module proves it on
the pockets where a sub-face-set `S` of `K.faces` can be cut out, with `F' = K.faces \ S`, and
leaves the rest as ONE residual.

* `gfaceWindCollapse_bd_iff` (proved): when `S ⊆ K.faces` and every boundary dart of `S` is on
  the walk of `K`, the boundary darts of `K.faces \ S` are the walk darts off `∂S`
  (`GFaceChoose.gfaceChoose_bd_exciseIn`).
* `gfaceWindCollapse_Excise K` (definition): a nonempty `S ⊆ K.faces` whose boundary darts are on
  the walk, keeping a relator cell of `K.faces` outside `S`, such that a finite sequence of cuts
  (`gfaceWindCollapse_CutStep`: a stretch of `∂S` darts that closes up or sits at one end) takes
  the walk to a list `c` of boundary darts of `K.faces \ S`, and such that the inverse source arc
  and the target arc each lie wholly on `∂S` or wholly off it.
* `gfaceWindCollapse_of_excise` (proved): the excision gives the nine clauses with
  `F' = K.faces \ S`.  Separation and the boundary clause by `gfaceWindCollapse_bd_iff`; the
  outer face, the source cell and `F' ≠ K.faces` from `S ⊆ K.faces`, `S` nonempty; the kept
  cell from the relator cell outside `S`; the chain clause by `gfaceWindCollapse_rt` (the filter
  of the walk is `c`, and `c` is a walk); the two block clauses by `gfaceWindCollapse_block`.
* `gfaceWindCollapse_Statement` (OPEN): `gfaceWindCell_CollapseStatement` with the extra
  hypothesis `¬ gfaceWindCollapse_Excise K`.
* `gfaceWindCollapse_collapse_of` (proved): the residual gives `gfaceWindCell_CollapseStatement`
  (split on `gfaceWindCollapse_Excise K`).
* `gfaceWindCollapse_of_collapse` (proved): the converse (drop the extra hypothesis).
* `gfaceWindCollapse_extremal` (proved): with `gfaceWindCell_NineStatement`, the residual gives
  `extremalGFaceProve_Statement` (`gfaceWindCell_extremal_of_cell`).

## LOUD: the residual is EQUIVALENT to `gfaceWindCell_CollapseStatement`, not strictly weaker

`gfaceWindCollapse_collapse_of` and `gfaceWindCollapse_of_collapse` prove both directions, so
`gfaceWindCollapse_Statement ↔ gfaceWindCell_CollapseStatement`.  No residual `R` can be both
strictly weaker than the collapse statement and have a proved reduction `R → collapse`; what is
smaller is the proof content: the residual only covers pockets with a `0`-cell where no excision
exists (in the sweeps below, 6% to 40% of the `0`-cell cases).

The collapse statement was NOT proved outright.  Heuristically it is as hard as the general
face-set flip statement: inserting a digon (a `0`-cell bounded by two parallel copies of an
interior edge) into a face set changes neither the area (relator cells only), least area, the
labels, nor the walk of `K`, so every configuration of relator cells reappears with a `0`-cell.
Surgery keeping `X` and `K` fixed cannot remove the digon; the lane forbids that route anyway.

## Truth check

Scratchpad `gl-p10-83/cut.py`.  It is a Lean-literal model built on the `gl-p10-78` models
(`extcx.py`), with the excision checked literally: the `∂S` darts on the walk, each arc wholly on
or off `∂S`, every interior maximal run of `∂S` darts closed, and a relator cell in
`K.faces \ S`.  Clauses are computed for `F' = K.faces \ S`, and by brute force over `F'` when no
excision exists.  Each sweep ran for 150 s.
* The `gfaceWindNine` counterexample: excisions `S = {2}` and `S = {1,2}`, both satisfying the
  clauses, i.e. `F' = {1,4}` and `F' = {4}`, the face sets found in `gl-p10-78`.  So the proved
  case covers the counterexample.
* Random seed 1: 26052 no-loop cases with a `0`-cell.  An excision exists in 24516 of them, and
  the clauses hold at `K.faces \ S` in all 24516 (0 failures).  In the other 1536 cases (the
  residual), the clauses hold for some `F'` in all 1536.
* Random seed 3: 40677 cases, 36878 excisions (36878 good, 0 bad), residual 3799 of 3799.
* Witness seed 2: 15624 cases, 9335 excisions (9335 good, 0 bad), residual 6289 of 6289.
So the residual holds on every model case.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

section Excise

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Boundary darts after an excision**: when `S ⊆ K.faces` and every boundary dart of `S` is on
the walk of `K`, the boundary darts of `K.faces \ S` are the walk darts off `∂S`. -/
theorem gfaceWindCollapse_bd_iff (K : PocketFaceSet D eps X lo hi)
    {S : Finset X.toCombMap.Face} (hSK : S ⊆ K.faces)
    (hSc : ∀ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d → d ∈ K.boundary.cycle)
    (x : X.toCombMap.Dart) :
    extremalGFaceProve_bd X.toCombMap (K.faces \ S) x = true ↔
      x ∈ K.boundary.cycle ∧ ¬ Surgery.MapCollapse.IsBoundaryDart X.toCombMap S x := by
  have hS : ∀ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d ↔
      d ∈ K.boundary.cycle.filter (extremalGFaceProve_bd X.toCombMap S) := by
    intro d
    rw [List.mem_filter, extremalGFaceProve_bd_eq_true_iff]
    exact ⟨fun h => ⟨hSc d h, h⟩, fun h => h.2⟩
  rw [GFaceChoose.gfaceChoose_bd_exciseIn K.boundary.cycle_mem_iff hS
    (fun d hd => (List.mem_filter.mp hd).1) hSK x, ← hS]
