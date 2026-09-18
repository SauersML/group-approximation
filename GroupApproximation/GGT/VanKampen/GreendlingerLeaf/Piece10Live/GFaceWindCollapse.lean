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

/-- **An excision** of a sub-face-set `S` from `K.faces`: `S` is nonempty, its boundary darts are
on the walk, a relator cell of `K.faces` lies outside `S`, a finite sequence of cuts takes the
walk to a list `c` of boundary darts of `K.faces \ S`, and each arc lies wholly on `∂S` or wholly
off it. -/
def gfaceWindCollapse_Excise (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (S : Finset X.toCombMap.Face) (c : List X.toCombMap.Dart), S ⊆ K.faces ∧ S.Nonempty ∧
    (∀ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d → d ∈ K.boundary.cycle) ∧
    (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ K.faces ∧ (cell X kept).face ∉ S) ∧
    Relation.ReflTransGen
      (gfaceWindCollapse_CutStep X.toCombMap (extremalGFaceProve_bd X.toCombMap (K.faces \ S)))
      K.boundary.cycle c ∧
    (∀ x ∈ c, extremalGFaceProve_bd X.toCombMap (K.faces \ S) x = true) ∧
    ((∀ d ∈ invDarts X K.sourceArc.darts,
        Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d) ∨
      ∀ d ∈ invDarts X K.sourceArc.darts,
        ¬ Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d) ∧
    ((∀ d ∈ K.targetArc.darts, Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d) ∨
      ∀ d ∈ K.targetArc.darts, ¬ Surgery.MapCollapse.IsBoundaryDart X.toCombMap S d)

/-- **The clauses from an excision**, with `F' = K.faces \ S`. -/
theorem gfaceWindCollapse_of_excise (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (h : gfaceWindCollapse_Excise K) :
    ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F' := by
  obtain ⟨S, c, hSK, ⟨s, hs⟩, hSc, ⟨kept, hkK, hkS⟩, hr, hcb, hsrc, htgt⟩ := h
  have hbd := gfaceWindCollapse_bd_iff K hSK hSc
  have hB : ∀ d, X.toCombMap.faceOf d ∈ K.faces \ S →
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ K.faces \ S → d ∈ K.boundary.cycle :=
    fun d h1 h2 => ((hbd d).mp ((extremalGFaceProve_bd_eq_true_iff _ _ d).mpr ⟨h1, h2⟩)).1
  have hfc : K.boundary.cycle.filter (extremalGFaceProve_bd X.toCombMap (K.faces \ S)) = c := by
    rw [(gfaceWindCollapse_rt hr hK.1).1]
    exact List.filter_eq_self.mpr hcb
  refine ⟨K.faces \ S, gfaceChoose_sep_of_bd hB, hB,
    fun ho => K.outerFace_not_mem (Finset.mem_sdiff.mp ho).1,
    fun hso => K.source_not_mem (Finset.mem_sdiff.mp hso).1,
    ⟨kept, Finset.mem_sdiff.mpr ⟨hkK, hkS⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro he
    have h1 : s ∈ K.faces \ S := by
      rw [he]
      exact hSK hs
    exact (Finset.mem_sdiff.mp h1).2 hs
  · rw [hfc]
    exact (gfaceWindCollapse_rt hr hK.1).2
  · refine gfaceWindCollapse_block K.sourceArc.darts _ ?_
    rcases hsrc with hon | hoff
    · refine Or.inr fun d hd => Bool.eq_false_iff.mpr fun ht => ?_
      exact ((hbd _).mp ht).2 (hon _ (gfaceWindNine_mem_src K hd))
    · exact Or.inl fun d hd => (hbd _).mpr
        ⟨extremalGFaceProve_alpha_mem_of_source K hd, hoff _ (gfaceWindNine_mem_src K hd)⟩
  · refine gfaceWindCollapse_block K.targetArc.darts _ ?_
    rcases htgt with hon | hoff
    · exact Or.inr fun d hd => Bool.eq_false_iff.mpr fun ht => ((hbd d).mp ht).2 (hon d hd)
    · exact Or.inl fun d hd => (hbd d).mpr ⟨extremalGFaceProve_mem_of_target K hd, hoff d hd⟩

end Excise

/-- **The `0`-cell residual off the excisions** (OPEN; EQUIVALENT to
`gfaceWindCell_CollapseStatement`, both directions proved below, see the module docstring).
Under the premises of `gfaceWindCell_CollapseStatement` and when no excision exists, some face
set `F'` satisfies `extremalGFaceProve_Clauses`. -/
def gfaceWindCollapse_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K → ¬ gfaceChoose_Loop K →
      ¬ gfaceWindCell_RCells K → ¬ gfaceWindCollapse_Excise K →
        ∃ F' : Finset X.toCombMap.Face, extremalGFaceProve_Clauses K F'

/-- **The `0`-cell residual from the residual off the excisions** (an excision by
`gfaceWindCollapse_of_excise`, the rest by the residual). -/
theorem gfaceWindCollapse_collapse_of (h : gfaceWindCollapse_Statement.{u, w, v}) :
    gfaceWindCell_CollapseStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR
  rcases Classical.em (gfaceWindCollapse_Excise K) with hE | hE
  · exact gfaceWindCollapse_of_excise K hK hE
  · exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR hE

/-- **The converse** (drop the extra hypothesis): the residual is equivalent to
`gfaceWindCell_CollapseStatement`. -/
theorem gfaceWindCollapse_of_collapse (h : gfaceWindCell_CollapseStatement.{u, w, v}) :
    gfaceWindCollapse_Statement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR _
  exact h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose hL hR

/-- **The face-set flip statement from the cell statement and the residual.** -/
theorem gfaceWindCollapse_extremal (h : gfaceWindCell_NineStatement.{u, w, v})
    (hC : gfaceWindCollapse_Statement.{u, w, v}) :
    extremalGFaceProve_Statement.{u, w, v} :=
  gfaceWindCell_extremal_of_cell h (gfaceWindCollapse_collapse_of hC)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_bd_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_Excise
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_of_excise
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_Statement
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_collapse_of
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_of_collapse
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_extremal
