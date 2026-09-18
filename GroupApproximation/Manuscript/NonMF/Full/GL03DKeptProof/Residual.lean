import GroupApproximation.Manuscript.NonMF.Full.GL03DKeptProof.Tools
import GroupApproximation.Manuscript.NonMF.Full.GL03D.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept sub-walk core with pinch segments allowed

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Infrastructure for `thm:hull` in `non_mf_groups_exist.tex` (around
line 2121); certifies no printed sentence on its own.

**NOT PROVED UNCONDITIONALLY.**  `GL03DKept.gl03dKept_KeptSubwalkCoreStatement` is not proved
here.  What stays open is planar content, not list combinatorics.  One must pick the kept walk
so that its side (a Jordan region of the planar map) avoids the exterior and the source cell,
holds a relator cell, and cuts both arcs in end blocks.

**Truth check.**  No counterexample to the core, or to the residual below, is known.
* On `P10RoseJunctionRefute` (24 darts, cycle `[0,2,16,4,6,18,8,20,10,12,22]`), keep only the
  loop dart `0`.  Then `B = [0]` is a pinch segment, since dart `0` is a loop on the cell `K0`.
  Its side is `{K0}`: a relator cell, and neither the exterior nor the source cell.  `q` is
  false on both arcs.  So every conjunct holds, and so does the original turning condition,
  because `σ(α 0) = 0`.
* On the 16-dart GL05c model, keeping the loop `[p]` works the same way.

**The residual** `gl03dKeptProof_PinchCoreStatement` has the hypotheses of the core.  It asks
for the same `q` with the same side conditions, but three conjuncts are weakened, and each
weakening is discharged here:

* **The walk part.**  It is either the core's (nonempty, chain, closing, turning) or a
  **pinch segment** (`gl03dKeptProof_PinchSegment`).  A pinch segment is a nonempty closing
  infix of the cycle with pairwise distinct start vertices.  It has no chain and no turning
  condition to check (`gl03dKeptProof_coreWalk_of_pinch`).
* **The `t_1⁻¹` end block.**  It is either the core's, or `q` is false on all of `t_1⁻¹`.
* **The `t_2` block.**  It is either the core's, or `q` is false on all of `t_2`.

Each weakening is a disjunction whose first disjunct is the core conjunct, so the core implies
the residual (`gl03dKeptProof_pinchCore_of_core`).  This is the truth witness: the residual is
false only if the core is.  The converse, `gl03dKeptProof_core_of_pinchCore`, is the reduction.
Proving the residual therefore needs strictly less than proving the core.  The walk conditions
are not checked: a minimal pinch, i.e. positions `i < j` of the cycle with the same start vertex
and `j - i` least, is automatically a simple closed walk.  Only the side and end-block
conditions remain, and those are the Jordan content.

Endpoint: `gl03dKeptProof_roseRegionMoveSubArc_of_pinchCore`, the statement `Full/GL06` needs,
from the residual.
-/

namespace GroupApproximation.Full.GL03DKeptProof

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **The kept sub-walk core with pinch segments allowed** (Osin Lemma 9.7(b), for `thm:hull`;
internal combinatorial statement, not a literature result).  The hypotheses of
`GL03DKept.gl03dKept_KeptSubwalkCoreStatement`, and its conclusion with three weakenings.  The
filter `B` is a noncrossing closed walk or a pinch segment.  `q` keeps an end block of `t_1⁻¹`
or nothing of it.  `q` keeps a prefix or suffix of `t_2`, or nothing of it. -/
def gl03dKeptProof_PinchCoreStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      GL06f.AllNonFirstTurnsCrossed K →
        ∃ q : X.toCombMap.Dart → Bool,
          (gl03dKeptProof_CoreWalk X.toCombMap (K.boundary.cycle.filter q) ∨
            gl03dKeptProof_PinchSegment X.toCombMap K.boundary.cycle
              (K.boundary.cycle.filter q)) ∧
          (∃ y ∈ K.boundary.cycle, q y = false) ∧
          (X.outerFace ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q) ∨
            ∃ d ∈ K.targetArc.darts, q d = true) ∧
          ((cell X K.source).face ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q) ∨
            ∃ d ∈ invDarts X K.sourceArc.darts, q d = true) ∧
          ((∃ kept : Fin X.rCellCount,
            (cell X kept).face ∈ sideFaces X.toCombMap (K.boundary.cycle.filter q)) ∨
            ∃ d ∈ K.boundary.cycle, q d = true ∧
              ∃ kept : Fin X.rCellCount, X.toCombMap.faceOf d = (cell X kept).face) ∧
          (GL05b.IsEndBlock q (invDarts X K.sourceArc.darts) ∨
            ∀ d ∈ invDarts X K.sourceArc.darts, q d = false) ∧
          ((∃ i, K.targetArc.darts.filter q = K.targetArc.darts.take i ∨
            (K.targetArc.darts.filter q = K.targetArc.darts.drop i ∧
              K.targetArc.start.1 + i ≤ (outerDarts X).length)) ∨
            ∀ d ∈ K.targetArc.darts, q d = false)

/-- **The core from the pinch-core residual** (Osin 9.7(b), `thm:hull` infrastructure).  A pinch
segment satisfies the walk part (`gl03dKeptProof_coreWalk_of_pinch`).  A `q` false on an arc
keeps its empty prefix. -/
theorem gl03dKeptProof_core_of_pinchCore
    (h : gl03dKeptProof_PinchCoreStatement.{u, w, v}) :
    GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  obtain ⟨q, hw, hy, hout, hsrcf, hrel, hT1, hT2⟩ :=
    h D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  obtain ⟨hchainK, -⟩ := hwalk
  obtain ⟨h1, h2, h3, h4⟩ :
      gl03dKeptProof_CoreWalk X.toCombMap (K.boundary.cycle.filter q) :=
    hw.elim id (gl03dKeptProof_coreWalk_of_pinch K.boundary q hchainK)
  refine ⟨q, h1, h2, h3, h4, hy, hout, hsrcf, hrel, ?_, ?_⟩
  · exact hT1.elim id gl03dKeptProof_isEndBlock_of_forall_false
  · rcases hT2 with hT2 | hT2
    · exact hT2
    · exact ⟨0, Or.inl (by rw [gl03dKeptProof_filter_eq_nil hT2, List.take_zero])⟩

/-- **The pinch-core residual from the core** (truth witness): every weakened conjunct has the
core conjunct as its first disjunct. -/
theorem gl03dKeptProof_pinchCore_of_core
    (h : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    gl03dKeptProof_PinchCoreStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  obtain ⟨q, h1, h2, h3, h4, hy, hout, hsrcf, hrel, hT1, hT2⟩ :=
    h D eps X lo hi hLA hlet K hwalk hft hsrc htgt hpin hrose
  exact ⟨q, Or.inl ⟨h1, h2, h3, h4⟩, hy, hout, hsrcf, hrel, Or.inl hT1, Or.inl hT2⟩

/-- **The sub-arc region move from the pinch-core residual** (Osin 9.7(b), `thm:hull`
infrastructure; conditional on `gl03dKeptProof_PinchCoreStatement`). -/
theorem gl03dKeptProof_roseRegionMoveSubArc_of_pinchCore
    (h : gl03dKeptProof_PinchCoreStatement.{u, w, v}) :
    GL06f.RoseRegionMoveSubArcStatement.{u, w, v} :=
  GL03D.gl03dKept_roseRegionMoveSubArc_of_core (gl03dKeptProof_core_of_pinchCore h)

end GroupApproximation.Full.GL03DKeptProof

#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_PinchCoreStatement
#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_core_of_pinchCore
#audit_axioms GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_pinchCore_of_core
#audit_axioms
  GroupApproximation.Full.GL03DKeptProof.gl03dKeptProof_roseRegionMoveSubArc_of_pinchCore
