import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.InPlace
import GroupApproximation.Meta.AxiomGuard

/-!
# The live rose reduction chain, part 1: the in-place step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module is the first half of the new-file replacement of
`P10Rose/Proof` (dead-route removal, part 2); the second half is `P10Rose/Live/Reduction`.

* `RoseInPlaceStepStatement` (OPEN): the rose step inside the same diagram.
* `combinatorialStep_of_inPlaceStep`: `RoseCombinatorialStepStatement` (module `P10Rose/Cut`) from
  it, with `X' = X`.
* `rose_of_inPlaceStep`: `P10ChordLift.RoseStepStatement` from it, via `rose_of_combinatorialStep`.
* `exists_succ_of_isClosedDartWalk`: a generic fact on closed dart walks, used by the sub-arc
  region-move reduction of `P10Rose/Live/Reduction`.

## Removed dead route

The filter route of the old modules is not copied.  `RoseFilterStepStatement`
(`P10Rose/InPlaceFilter`) and `RoseRegionMoveStatement` (`P10Rose/FilterMove`) were FALSE: both keep
the two arcs entire, and the three-petal flower `c = [p₃] ++ [q₃] ++ [p₁, q₁, p₂] ++ [q₂]` admits no
such step (its only step `F' = {P₁, P₃}` removes `p₂`, a dart of the target arc, and needs
`t₂' = zeroArc t₂`).  Their reductions `inPlaceStep_of_filterStep` and `rose_of_filterStep` are
removed.  The corrected statements are `RoseInPlaceStepStatement` (here) and
`RoseRegionMoveSubArcStatement` (module `P10Rose/Live/Reduction`), which let the new arcs be proper
sub-arcs and re-list the kept darts by a permutation.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

/-- **The rose step in place** (OPEN; a remaining gap of `P10Rose`).  Under the hypotheses of
`RoseCombinatorialStepStatement`, some pocket face set of the same diagram is in walk order, has
proper arcs and strictly fewer repeated visits.  Its intended proof chooses a new face set and
applies `step_of_faces`, `step_of_lobe` or `step_of_absorb` (module `P10Rose/InPlace`).  Not
refuted: the three-petal flower has the step `F' = {P₁, P₃}`. -/
def RoseInPlaceStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
          K'.sourceArc.length < (cellDarts X K'.source).length ∧
          K'.targetArc.length < (outerDarts X).length ∧
          K'.repeatedVisits < K.repeatedVisits

/-- **The combinatorial rose step from the in-place one**, keeping the diagram. -/
theorem combinatorialStep_of_inPlaceStep (h : RoseInPlaceStepStatement.{u, w, v}) :
    RoseCombinatorialStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨K', hK', hsrc', htgt', hlt⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨X, K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hK', hsrc', htgt', hlt⟩

/-- **The rose step from the in-place one.** -/
theorem rose_of_inPlaceStep (h : RoseInPlaceStepStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_combinatorialStep (combinatorialStep_of_inPlaceStep h)

/-- Every dart of a closed dart walk ends where some dart of the walk begins. -/
theorem exists_succ_of_isClosedDartWalk {M : CombMap.{v}} {L : List M.Dart}
    (hw : IsClosedDartWalk M L) {x : M.Dart} (hx : x ∈ L) :
    ∃ x' ∈ L, M.vertexOf (M.alpha x) = M.vertexOf x' := by
  obtain ⟨P, Q, rfl⟩ := List.append_of_mem hx
  have h1 : IsClosedDartWalk M ((P ++ [x]) ++ Q) := by
    rw [List.append_assoc]
    exact hw
  have h2 : IsClosedDartWalk M (Q ++ (P ++ [x])) := h1.append_comm
  have h3 : IsClosedDartWalk M ((Q ++ P) ++ [x]) := by
    rw [List.append_assoc]
    exact h2
  obtain ⟨hne, -, hclose⟩ := h3
  have hl : ((Q ++ P) ++ [x]).getLast hne = x := List.getLast_concat
  rw [hl] at hclose
  refine ⟨((Q ++ P) ++ [x]).head hne, ?_, hclose⟩
  rcases List.mem_append.mp (List.head_mem hne) with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
    · exact List.mem_append.mpr (Or.inl h)
  · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseInPlaceStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.combinatorialStep_of_inPlaceStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_inPlaceStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.exists_succ_of_isClosedDartWalk
