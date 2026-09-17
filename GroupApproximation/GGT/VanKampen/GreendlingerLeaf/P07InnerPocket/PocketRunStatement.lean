import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Runs follow their piece: corrected statement (lane `gl-p07-09`)

## LOUD: the lane statement is FALSE AS STATED

The lane claims two things.  First, that two cyclically consecutive walk darts on `G₁.darts` are
consecutive under `facePerm`.  Second, that every maximal `G₁`-run is a single sub-arc.  Neither
follows from `EnclosedFaceSetSucc` or from lane 06's `Hyp`.

A counter-model is a pinched cell `Π_i`: its boundary touches itself at a vertex `v`.  Let `G₁` be
one lobe `v → v`, and put the outer face across the other lobe.  At the last dart `d` of `G₁`,
`facePerm d` starts the other lobe, which is not on the walk.  So the walk turns straight on to
`G₁[0]`, and the run is `G₁[s..] ++ G₁[..t]`, which is not a sub-arc.  See the module docstring of
`PocketRunStep`.

## Corrected statement (proved here, Hyp-free)

Take any `EnclosedFaceSetSucc X F ow`, any arc `A` of a cell `k` whose darts are walk darts, and any
rotation `ow.rotate n = u ++ v` whose block `u` lies on `A`.

1. **Unconditionally**, `u` is the concatenation of at most two sub-arcs of `cellDarts X k`.
2. Suppose every dart of `u` whose `facePerm` leaves `A` is pinch-free.  This is at most one dart,
   the last dart of `A`.  Then `u` is a single sub-arc `B`, and the inverse walk splits as
   `invDarts (ow.rotate n) = invDarts v ++ invDarts B.darts`.

Proof: the two-piece and one-piece results are `PocketRun.exists_two_cyclicArc_of_run` and
`PocketRun.exists_cyclicArc_of_run`, applied to the rotated walk `EnclosedFaceSetSucc.rotate E n`
(lane 13).  The inverse walk splits by `reverse_append` and `map_append`.

**Downstream gap.**  Lanes that want a single `G₁`-arc need pinch-freeness at the last dart of
`G₁`, or they must handle the two-piece case.  We do not state that as a residual Statement,
because under the present `Hyp` it can fail (see the model).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded SimpleClosedWalkSides

universe u w v

/-- **Lane gl-p07-09, corrected statement.**  A walk block on an arc is at most two sub-arcs.  It
is one sub-arc when the dart that leaves the arc is pinch-free, and then the inverse walk splits
accordingly. -/
def PocketRunInfixStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (X : DiscDiagram.{u, w, v} W) (F : Finset X.toCombMap.Face) (ow : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X F ow → ∀ (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
    (∀ x ∈ A.darts, x ∈ ow) → ∀ (n : ℕ) (u v : List X.toCombMap.Dart), ow.rotate n = u ++ v →
    (∀ x ∈ u, x ∈ A.darts) →
      (∃ B₁ B₂ : CyclicArc (cellDarts X k), u = B₁.darts ++ B₂.darts) ∧
      ((∀ x ∈ u, X.toCombMap.facePerm x ∉ A.darts → PocketRun.PinchFreeAt X.toCombMap x) →
        ∃ B : CyclicArc (cellDarts X k), B.darts = u ∧
          invDarts X (ow.rotate n) = invDarts X v ++ invDarts X B.darts)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunInfixStatement

/-- **Lane gl-p07-09, proof of the corrected statement.** -/
theorem pocketRunInfix : PocketRunInfixStatement.{u, w, v} := by
  intro G _ Lambda W X F ow E k A hAow n u v hsplit hu
  have E' := EnclosedFaceSetSucc.rotate E n
  have hAw : ∀ x ∈ A.darts, x ∈ ow.rotate n := fun x hx => List.mem_rotate.mpr (hAow x hx)
  refine ⟨PocketRun.exists_two_cyclicArc_of_run E' hsplit k A hAw hu, fun hpinch => ?_⟩
  obtain ⟨B, hB⟩ := PocketRun.exists_cyclicArc_of_run E' hsplit k A hAw hu hpinch
  refine ⟨B, hB, ?_⟩
  rw [hsplit, hB]
  simp only [invDarts, List.reverse_append, List.map_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketRunInfix

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
