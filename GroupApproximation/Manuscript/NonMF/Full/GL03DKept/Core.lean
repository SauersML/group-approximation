import GroupApproximation.Manuscript.NonMF.Full.GL03DKept.Filter
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept sub-walk statement with its generic part removed

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Infrastructure for `thm:hull` in `non_mf_groups_exist.tex` (around
line 2121); certifies no printed sentence on its own.

**Residual, stated loudly.**  `Full.GL03D.KeptSubwalkStatement` is not proved here.  It is not
list combinatorics: it asks for a sub-walk of the pocket boundary whose side (a Jordan region of
the planar map) avoids the exterior and the source cell and holds a relator cell, with end blocks
on both arcs.  This module isolates `gl03dKept_KeptSubwalkCoreStatement`, which asks for the same
choice `q` but with less to check:

* the noncrossing walk is asked only for nonemptiness, chain, closing and the turning condition;
  duplicate-freeness and one-way edges are automatic (`gl03dKept_isNoncrossing_filter`);
* the exterior may lie on the side, provided `q` keeps a dart of `t_2` (across it lies the
  exterior, which is then off the side);
* the source cell may lie on the side, provided `q` keeps a dart of `t_1⁻¹`;
* the side need not be shown to hold a relator cell, provided `q` keeps a dart on one.

`gl03dKept_keptSubwalk_of_core` proves the original from the core, and
`gl03dKept_core_of_keptSubwalk` the converse, so the core is exactly as true as the original, with
strictly less proof content.  No counterexample to either is known: on the 16-dart GL05c model the
choice keeping only the loop `[p]` (or the lobe `[R1a, q1, R1b]`) satisfies every conjunct.
-/

namespace GroupApproximation.Full.GL03DKept

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

/-- **The core of the kept sub-walk statement** (Osin Lemma 9.7(b), for `thm:hull`; internal
combinatorial statement, not a literature result).  Hypotheses of
`Full.GL03D.KeptSubwalkStatement`.  Conclusion: a choice `q` of boundary darts whose filter
`B` is a nonempty closed walk in cycle order with the noncrossing turning condition, dropping some
dart, whose side avoids the exterior unless `B` meets `t_2`, avoids the source cell unless `B`
meets `t_1⁻¹`, and holds a relator cell unless `B` has a dart on one, keeping an end block of
`t_1⁻¹` and a prefix or suffix of `t_2`. -/
def gl03dKept_KeptSubwalkCoreStatement : Prop :=
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
          K.boundary.cycle.filter q ≠ [] ∧
          (K.boundary.cycle.filter q).IsChain (fun d e =>
            X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
          (∀ hne : K.boundary.cycle.filter q ≠ [],
            X.toCombMap.vertexOf (X.toCombMap.alpha ((K.boundary.cycle.filter q).getLast hne)) =
              X.toCombMap.vertexOf ((K.boundary.cycle.filter q).head hne)) ∧
          (∀ d ∈ K.boundary.cycle.filter q, ∀ m : ℕ, 0 < m →
            walkKeep X.toCombMap (K.boundary.cycle.filter q)
              ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha d)) →
            (∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap (K.boundary.cycle.filter q)
              ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) →
            (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) ∈ K.boundary.cycle.filter q) ∧
          (∃ y ∈ K.boundary.cycle, q y = false) ∧
          (X.outerFace ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q) ∨
            ∃ d ∈ K.targetArc.darts, q d = true) ∧
          ((cell X K.source).face ∉ sideFaces X.toCombMap (K.boundary.cycle.filter q) ∨
            ∃ d ∈ invDarts X K.sourceArc.darts, q d = true) ∧
          ((∃ kept : Fin X.rCellCount,
            (cell X kept).face ∈ sideFaces X.toCombMap (K.boundary.cycle.filter q)) ∨
            ∃ d ∈ K.boundary.cycle, q d = true ∧
              ∃ kept : Fin X.rCellCount, X.toCombMap.faceOf d = (cell X kept).face) ∧
          GL05b.IsEndBlock q (invDarts X K.sourceArc.darts) ∧
          ∃ i, K.targetArc.darts.filter q = K.targetArc.darts.take i ∨
            (K.targetArc.darts.filter q = K.targetArc.darts.drop i ∧
              K.targetArc.start.1 + i ≤ (outerDarts X).length)

end GroupApproximation.Full.GL03DKept

#audit_axioms GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement
