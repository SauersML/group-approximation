import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWrapRoseRescue
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The wrap rose under first-turn order

Model tests for first-turn order (`FirstTurn`, `Estimating/OsinPocketFirstTurnWalk.lean`) on the
three-petal rose `OsinPocketWrapRose.wrapDiagram`.  A pocket face set `K` is in first-turn order
when its complement spelling `c = K.boundary.cycle.reverse.map alpha` is a first-turn walk:
`c.IsChain (FirstTurn M c)` and `FirstTurn M c (c.getLast _) (c.head _)`.

The rose refutes `PocketPinchLabelledStatement` at `ε = 0` with the pocket face set `wrapK`
(`OsinPocketWrapRose.pocketPinchWrapRefutation`).  At `ε ≥ 1` the same rose carries the simple
pocket face set `rescueK` (`OsinPocketWrapRoseRescue`).

* `wrap_complement`: the complement spelling of `wrapK` is `[3,1]`.
* `wrap_not_firstTurn_three_one` and `wrap_not_firstTurn_one_three`: neither turn of `[3,1]` is a
  first turn.  The first rotation from the reversal `2` of `3` is `3`, and from the reversal `0`
  of `1` it is `1`; both are darts of the walk, and neither is the target.
* `wrap_not_firstTurnWalk`: `[3,1]` fails the chain and the closing turn, so `wrapK` is not in
  first-turn order.
* `rescue_complement` and `rescue_firstTurn`: the complement spelling of `rescueK` is `[4]`, and
  rotating five steps from the reversal `5` of `4` reaches `4` past the darts `0,1,2,3`, none of
  which lies on an edge of `[4]`.
* `WrapRoseFirstTurnModel`, `wrapRoseFirstTurnModel`: the refuting pocket lies outside first-turn
  order, and the simple rescue at every `ε ≥ 1` is in first-turn order.

So the refutation at `ε = 0` does not reach the pinch restricted to first-turn order, and the
repaired pinch at `ε ≥ 1` has a first-turn witness on the rose.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn

open Equiv SimpleClosedWalkSides
open OsinPocketWrapRose
open OsinPocketWrapRoseRescue

/-- The complement spelling of `wrapK` is `[3,1]`. -/
theorem wrap_complement :
    wrapK.boundary.cycle.reverse.map wrapDiagram.toCombMap.alpha = ([3, 1] : List (Fin 6)) := by
  change ([0, 2] : List (Fin 6)).reverse.map roseAlpha = ([3, 1] : List (Fin 6))
  decide

/-- **The turn from `3` is not a first turn.**  The first rotation from the reversal `2` of `3` is
`3`, a dart of `[3,1]`, and it is not `1`. -/
theorem wrap_not_firstTurn_three_one : ¬ FirstTurn M ([3, 1] : List (Fin 6)) 3 1 := by
  rintro ⟨k, hk, hky, havoid⟩
  rcases Nat.lt_or_ge 1 k with h1 | h1
  · exact havoid 1 Nat.zero_lt_one h1 (by rw [pow_one]; exact Or.inl (by decide))
  · obtain rfl : k = 1 := by omega
    rw [pow_one] at hky
    exact absurd hky (by decide)

/-- **The turn from `1` is not a first turn.**  The first rotation from the reversal `0` of `1` is
`1`, a dart of `[3,1]`, and it is not `3`. -/
theorem wrap_not_firstTurn_one_three : ¬ FirstTurn M ([3, 1] : List (Fin 6)) 1 3 := by
  rintro ⟨k, hk, hky, havoid⟩
  rcases Nat.lt_or_ge 1 k with h1 | h1
  · exact havoid 1 Nat.zero_lt_one h1 (by rw [pow_one]; exact Or.inl (by decide))
  · obtain rfl : k = 1 := by omega
    rw [pow_one] at hky
    exact absurd hky (by decide)

/-- **`[3,1]` is not a first-turn walk**, along the chain or at the closing turn. -/
theorem wrap_not_firstTurnWalk :
    ¬ ([3, 1] : List (Fin 6)).IsChain (FirstTurn M ([3, 1] : List (Fin 6))) ∧
      ¬ FirstTurn M ([3, 1] : List (Fin 6)) 1 3 :=
  ⟨fun h => wrap_not_firstTurn_three_one (List.isChain_pair.mp h), wrap_not_firstTurn_one_three⟩

/-- The complement spelling of `rescueK` is `[4]`. -/
theorem rescue_complement (eps : ℕ) (heps : 1 ≤ eps) :
    (rescueK eps heps).boundary.cycle.reverse.map wrapDiagram.toCombMap.alpha =
      ([4] : List (Fin 6)) := by
  change ([5] : List (Fin 6)).reverse.map roseAlpha = ([4] : List (Fin 6))
  decide

/-- **The closing turn of `[4]` is a first turn.**  Rotating five steps from the reversal `5` of
`4` reaches `4`, past the darts `0, 1, 2, 3`, none of which lies on an edge of `[4]`. -/
theorem rescue_firstTurn : FirstTurn M ([4] : List (Fin 6)) 4 4 := by
  refine ⟨5, by decide, by decide, ?_⟩
  intro t ht0 ht5
  interval_cases t <;> simp only [walkKeep] <;> decide

/-- **The wrap rose under first-turn order** (model test).  The rose's map is `M`.  The pocket face
set `wrapK` refuting the pinch at `ε = 0` is not in first-turn order: its complement spelling
`[3,1]` fails the chain and the closing turn.  For every `ε ≥ 1` the simple pocket face set
`rescueK` of the same rose is in first-turn order: its complement spelling `[4]` has one dart and
closes by a first turn. -/
def WrapRoseFirstTurnModel : Prop :=
  wrapDiagram.toCombMap = M ∧
    (wrapK.boundary.cycle.reverse.map wrapDiagram.toCombMap.alpha = ([3, 1] : List (Fin 6)) ∧
      ¬ ([3, 1] : List (Fin 6)).IsChain (FirstTurn M ([3, 1] : List (Fin 6))) ∧
      ¬ FirstTurn M ([3, 1] : List (Fin 6)) 1 3) ∧
    ∀ eps : ℕ, ∀ heps : 1 ≤ eps, (rescueK eps heps).Simple ∧
      (rescueK eps heps).boundary.cycle.reverse.map wrapDiagram.toCombMap.alpha =
          ([4] : List (Fin 6)) ∧
        FirstTurn M ([4] : List (Fin 6)) 4 4

theorem wrapRoseFirstTurnModel : WrapRoseFirstTurnModel :=
  ⟨rfl, ⟨wrap_complement, wrap_not_firstTurnWalk.1, wrap_not_firstTurnWalk.2⟩,
    fun eps heps => ⟨rescueK_simple eps heps, rescue_complement eps heps, rescue_firstTurn⟩⟩

end GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.wrap_complement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.wrap_not_firstTurn_three_one
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.wrap_not_firstTurn_one_three
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.wrap_not_firstTurnWalk
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.rescue_complement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.rescue_firstTurn
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketWrapRoseFirstTurn.wrapRoseFirstTurnModel
