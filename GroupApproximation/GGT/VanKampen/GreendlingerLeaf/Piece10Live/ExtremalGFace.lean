import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapAssembly
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# The G-face tolerant flip: a union of walk regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-47.

Lane gl-p10-40 refuted every single-class extremal statement of the Piece 10 route
(`RoseExtremalClassStatement`, `P10ExtremalWrap.RoseExtremalBlockNoWrapStatement`, ...): in its
model (a cactus at a cut vertex, `scratchpad/gl-p10-40/WITNESS.txt`) the pocket carries G-faces,
inner faces that are no relator cells, and every single walk region either holds the only kept
relator cell, or holds the source or exterior face, or leaves a stretch that is not linked.
The flip of one region cannot remove all G-face regions at once.

The fix keeps the move of `P10ExtremalWrap.step_of_regionMove`, which already works for an
arbitrary colouring `z` constant along the walk regions, and flips a *union* of walk regions.
In the gl-p10-40 model `z` marks the four G-face regions inside `K` (faces `f2 f3 f4 f6`); the
flipped face set is the kept monogon `{f0}`, with boundary `[a0]`, and the repeated visits drop
from `4` to `0`.

* `extremalGFace_Clauses K z`: `z` is constant along the walk regions, flips no side pair of a
  walk dart, keeps the exterior face out, the source face out and some relator cell in, touches
  the cycle, and the kept darts `K.boundary.cycle.filter (movePred z)` are non-empty, form a walk
  in cycle order, and form one block on each of `K.sourceArc` and `K.targetArc`.
* `extremalGFace_Statement` (OPEN, TRUE on all checks below): under the premises of
  `RoseInPlaceStepNoWrapStatement`, some colouring satisfies `extremalGFace_Clauses`.
* `extremalGFace_step` (proved): the clauses give the in-place step, pointwise.
* `extremalGFace_inPlaceStepNoWrap`, `extremalGFace_stepNoWrap`,
  `extremalGFace_relativeGreendlinger` (proved): the endpoints, down to
  `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` with the four-piece-off residual.
* `Piece10Live/ExtremalGFaceOld`: the single-class no-wrap block statement implies
  `extremalGFace_Statement` (`z := regionColour r`), so the new statement is weaker; it is
  strictly weaker since it holds in the gl-p10-40 model where the old one fails.

## Truth check

Scratchpad `gl-p10-47/gface.py` (Lean-faithful: `facePerm d = sigma (alpha d)`, first turns,
rotation sectors, crossed turns, `FaceClassStep`, `flipFaces`, `movePred`) with the worst case
of relator cells `{source, kept}` only: the gl-p10-40 witness passes for all 181 decompositions
and all five choices of kept face (905 cases, one needs a union of regions).  Random planar maps
(`gface.py`, up to eight edges: 6849 instances) and loop-heavy maps (`search2.py`: 31571
instances) give no violation, but also no case that needs a union: they almost never reach the
G-face regime, so the evidence there rests on the witness.  The search does not model least area
or labels.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The clauses of a flip at a union of walk regions**, marked by `z`. -/
def extremalGFace_Clauses (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart → Bool) :
    Prop :=
  (∀ x y, CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle) x y →
    z x = z y) ∧
  (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
  X.outerFace ∉ flipFaces X.toCombMap K.faces z ∧
  (cell X K.source).face ∉ flipFaces X.toCombMap K.faces z ∧
  (∃ kept : Fin X.rCellCount, (cell X kept).face ∈ flipFaces X.toCombMap K.faces z) ∧
  (∃ y ∈ K.boundary.cycle, movePred X.toCombMap z y = false) ∧
  K.boundary.cycle.filter (movePred X.toCombMap z) ≠ [] ∧
  ((K.boundary.cycle.filter (movePred X.toCombMap z)).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
    K.sourceArc.darts.filter (movePred X.toCombMap z) = mid) ∧
  (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
    K.targetArc.darts.filter (movePred X.toCombMap z) = mid)

/-- **The in-place step from a flip at a union of walk regions**, pointwise: `t₁` is the sub-arc
of `K.sourceArc` reading its kept block, `t₂` the non-wrapping sub-arc of `K.targetArc` reading
its kept block, `s₁, s₂` the kept darts of the sides; the listing is the filtered cycle
(`P10ExtremalResidual.filter_decomposition`), and `step_of_regionMove` flips. -/
theorem extremalGFace_step (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hwrap : hi ≤ (outerDarts X).length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hsrc : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {z : X.toCombMap.Dart → Bool} (h : extremalGFace_Clauses K z) :
    ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
      K'.sourceArc.length < (cellDarts X K'.source).length ∧
      K'.targetArc.length < (outerDarts X).length ∧ K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨hz, hind, hout, hsource, ⟨_, hkept⟩, ⟨_, hy, hpy⟩, hne, hch,
      ⟨pre₁, mid₁, post₁, hs₁, hf₁⟩, ⟨pre₂, mid₂, post₂, hs₂, hf₂⟩⟩ := h
  have hnw : P10ExtremalResidual.TargetBlockNoWrap K pre₂ := targetBlockNoWrap_of_le K hwrap hs₂
  have hp : ∀ d, movePred X.toCombMap z (X.toCombMap.alpha d) = movePred X.toCombMap z d :=
    fun d => P10ExtremalResidual.movePred_alpha X.toCombMap z d
  have ht₁ := P07InnerPocket.CyclicArc.subArcArc_darts K.sourceArc pre₁ mid₁ post₁ hs₁
  have ht₂ := P10ExtremalResidual.noWrapSubArc_darts K.targetArc pre₂ mid₂ post₂ hs₂ hnw
  have hlen₁ := P07InnerPocket.CyclicArc.length_add_of_darts_eq K.sourceArc hs₁
  have hlen₂ := P07InnerPocket.CyclicArc.length_add_of_darts_eq K.targetArc hs₂
  have hlist := (P10ExtremalResidual.filter_decomposition X (movePred X.toCombMap z) hp
    K.decomposition (hf₁.trans ht₁.symm) (hf₂.trans ht₂.symm)).symm
  have hchain := hch
  rw [← hlist] at hchain
  have hwalk := P10RoseExtremal.isClosedDartWalk_of_perm_filter K.boundary.cycle_nodup
    K.boundary.cycle_mem_iff hz hind (List.Perm.of_eq hlist)
    (fun hnil => hne (hlist.symm.trans hnil)) hchain
  refine step_of_regionMove K hK hlabel hz hind hout hy hpy hsource hkept (List.Perm.of_eq hlist)
    hwalk ((List.length_filter_le _ _).trans K.firstSide_length_le)
    ((List.length_filter_le _ _).trans K.secondSide_length_le) ?_ ?_ ?_ ?_
  · show lo ≤ K.targetArc.start.1 + pre₂.length
    have := K.lo_le
    omega
  · show K.targetArc.start.1 + pre₂.length + mid₂.length ≤ hi
    have := K.le_hi
    omega
  · show mid₁.length < (cellDarts X K.source).length
    omega
  · show mid₂.length < (outerDarts X).length
    omega

end Clauses

/-- **The G-face tolerant flip statement** (OPEN, TRUE on the checks of the module docstring).
Under the premises of `RoseInPlaceStepNoWrapStatement`, some colouring `z` of the walk regions
satisfies `extremalGFace_Clauses`. -/
def extremalGFace_Statement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ z : X.toCombMap.Dart → Bool, extremalGFace_Clauses K z

/-- **The no-wrap in-place step from the G-face tolerant flip statement.** -/
theorem extremalGFace_inPlaceStepNoWrap (h : extremalGFace_Statement.{u, w, v}) :
    RoseInPlaceStepNoWrapStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨z, hz⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact extremalGFace_step (z := z) K hK hwrap hlabel hsrc htgt hz

/-- **The no-wrap outer-pinch step from the G-face tolerant flip statement.** -/
theorem extremalGFace_stepNoWrap (h : extremalGFace_Statement.{u, w, v}) :
    PocketOuterPinchStepSectionNoWrapStatement.{u, w, v} :=
  stepNoWrap_of_inPlaceStepNoWrap (extremalGFace_inPlaceStepNoWrap h)

/-- **Osin's Lemma 4.4 at least-area diagrams from the four-piece-off residual and the G-face
tolerant flip statement**: the term of `relativeGreendlinger_of_residualsNoWrap` with the step
from `extremalGFace_stepNoWrap`. -/
theorem extremalGFace_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : extremalGFace_Statement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlinger_of_binderFiveBelowNoWrap Piece01.proof.{u, w, v} Piece04.proof.{u, w, v}
    (P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (P06Bypass.refutedBelowSection_of_innerPocketEnclosed
        (P07InnerPocket.innerPocketEnclosed_of_fourPieceOff hoff)))
    (extremalGFace_stepNoWrap h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_Clauses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_Statement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_inPlaceStepNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_stepNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.extremalGFace_relativeGreendlinger
