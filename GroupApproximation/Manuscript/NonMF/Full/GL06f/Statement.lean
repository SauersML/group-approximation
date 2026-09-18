import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Manuscript.NonMF.Full.GL05b.RegionArcs
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose step and the sub-arc region move: statements

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, in the case where every non-first turn of the boundary cycle is crossed
by another passage (the rose configuration).

This module restates, with the same statement shapes, vocabulary whose original modules are not
wired or not WIP-free:

* `flipFaces M faces z`: the face set after a move along a colouring `z` of darts
  (shape of `GreendlingerLeaf/P10Rose/FilterMove.lean`).
* `TurnCrossed`, `NonFirstTurn`, `AllNonFirstTurnsCrossed`, `RoseStepStatement`
  (shape of `GreendlingerLeaf/P10ChordLift/Predicate.lean`).  `List.next` needs decidable
  equality of darts, supplied here classically.
* `RoseRegionMoveSubArcStatement` (shape of `GreendlingerLeaf/P10Rose/SubArc.lean`), with the
  move predicate `GL05b.movePred` and the names above.

The reduction `RoseRegionMoveSubArcStatement → RoseStepStatement` is in
`Full/GL06f/Reduction.lean`.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`; Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06f

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

open Classical in
/-- **The face set after a move** (for `thm:hull`): the faces whose membership in `faces` agrees
with `z = false`. -/
noncomputable def flipFaces (M : CombMap.{v}) (faces : Finset M.Face) (z : M.Dart → Bool) :
    Finset M.Face :=
  Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧ (M.faceOf x ∈ faces ↔ z x = false)

section Vocabulary

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

open Classical in
/-- **A crossed turn** (Osin Lemma 9.7(b), for `thm:hull`).  The turn `d₀ → next d₀` of the
boundary cycle is crossed by another passage: some cycle dart `d ≠ d₀` with `alpha d` at the vertex
of `alpha d₀` has exactly one of `alpha d` and `next d` strictly inside the rotation sector from
`alpha d₀` to `next d₀`. -/
def TurnCrossed (K : PocketFaceSet D eps X lo hi) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ∃ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle), d ≠ d₀ ∧
    X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
    ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha d) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next d hd))

open Classical in
/-- **A non-first turn** (for `thm:hull`).  The turn `d₀ → next d₀` is not a first turn along the
edges of the cycle. -/
def NonFirstTurn (K : PocketFaceSet D eps X lo hi) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
    (X.toCombMap.alpha (K.boundary.cycle.next d₀ hd₀)) (X.toCombMap.alpha d₀)

/-- **The rose configuration** (for `thm:hull`): every non-first turn of the boundary cycle is
crossed by another passage. -/
def AllNonFirstTurnsCrossed (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
    NonFirstTurn K d₀ hd₀ → TurnCrossed K d₀ hd₀

end Vocabulary

/-- **The rose case of the outer-pinch step** (Osin Lemma 9.7(b), for `thm:hull`).  The outer-pinch
step under the extra hypothesis that every non-first turn of the boundary cycle is crossed by
another passage: a pocket with strictly fewer repeated visits in an `O`-equivalent diagram. -/
def RoseStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, GroupApproximation.Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  K.targetArc.length < (outerDarts X).length →
                  ¬Unpinched X.toCombMap K.faces →
                  AllNonFirstTurnsCrossed K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The sub-arc region move** (Osin Lemma 9.7(b), for `thm:hull`).  In the rose configuration
there is a colouring `z` of darts, constant on the face classes of the boundary walk and never
flipping both sides of a boundary edge, such that the moved face set `flipFaces K.faces z` avoids
the exterior face, loses some boundary dart, separates a source cell from a kept cell, and has its
kept boundary darts rearranged into a closed walk `s_1 t_1 s_2 t_2` of the pocket shape. -/
def RoseRegionMoveSubArcStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      AllNonFirstTurnsCrossed K →
        ∃ z : X.toCombMap.Dart → Bool,
          (∀ x y, CombMap.FaceClassStep X.toCombMap
            (walkKeep X.toCombMap K.boundary.cycle) x y → z x = z y) ∧
          (∀ d ∈ K.boundary.cycle, z d = false ∨ z (X.toCombMap.alpha d) = false) ∧
          X.outerFace ∉ flipFaces X.toCombMap K.faces z ∧
          (∃ y ∈ K.boundary.cycle, GL05b.movePred X.toCombMap z y = false) ∧
          ∃ (source kept : Fin X.rCellCount),
            (cell X source).face ∉ flipFaces X.toCombMap K.faces z ∧
            (cell X kept).face ∈ flipFaces X.toCombMap K.faces z ∧
            ∃ (t₁ : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
              (s₁ s₂ : List X.toCombMap.Dart),
              List.Perm (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts)
                (K.boundary.cycle.filter (GL05b.movePred X.toCombMap z)) ∧
              IsClosedDartWalk X.toCombMap (s₁ ++ invDarts X t₁.darts ++ s₂ ++ t₂.darts) ∧
              s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ lo ≤ t₂.start.1 ∧
              t₂.start.1 + t₂.length ≤ hi ∧
              t₁.length < (cellDarts X source).length ∧ t₂.length < (outerDarts X).length

end GroupApproximation.Full.GL06f

#audit_axioms GroupApproximation.Full.GL06f.flipFaces
#audit_axioms GroupApproximation.Full.GL06f.TurnCrossed
#audit_axioms GroupApproximation.Full.GL06f.NonFirstTurn
#audit_axioms GroupApproximation.Full.GL06f.AllNonFirstTurnsCrossed
#audit_axioms GroupApproximation.Full.GL06f.RoseStepStatement
#audit_axioms GroupApproximation.Full.GL06f.RoseRegionMoveSubArcStatement
