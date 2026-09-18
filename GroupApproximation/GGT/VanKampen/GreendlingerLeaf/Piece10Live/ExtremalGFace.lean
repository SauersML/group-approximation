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
and all five choices of kept face; random planar maps (`gface.py`, up to eight edges) and
G-face-biased maps (`search2.py`: loop-heavy maps, perturbations of the witness) give no
violation.  The search does not model least area or labels.

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
