import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.Meta.AxiomGuard

/-!
# Both reclosings of a noncrossing closed walk whose passages do not interleave

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`PocketRegion.ofNoncrossingClosedWalkEuler` (`Estimating/OsinPocketKeptCellSection`) builds a
pocket region from the Euler equalities of the two reclosings of a noncrossing closed walk, with no
following boundary cycle.  `IsNoncrossingClosedWalk.reclosed_euler` gives the inner equality only
when the outer cycle follows its boundary, and a walk touching itself once in each way has neither
cycle following (`OsinPocketCellWalkFollowsModel.doubleTouchNeitherFollows`).

A count avoids following.  For a noncrossing closed walk `w` in a planar map `M`:
* both reclosings together have `|w|` more edges and two more faces than `M`
  (`IsNoncrossingClosedWalk.edgeCount_add`, `IsNoncrossingClosedWalk.faceCount_add`), with no
  following hypothesis;
* each reclosing is connected (`Surgery.MapCollapse.reclosedMap_connected`), so its Euler
  characteristic is at most two (`CombMap.eulerCharacteristic_le_two`);
* so once the two reclosings together have at least `|w|` more vertices than `M`, both Euler
  characteristics are two (`IsNoncrossingClosedWalk.eulers_of_vertexCount_le`).

The vertex count needs a hypothesis beyond noncrossing.  In the rose with darts `0, …, 5`,
`alpha = (0 1)(2 3)(4 5)` and `sigma : 1 ↦ 0 ↦ 3 ↦ 2 ↦ 5 ↦ 4 ↦ 1`, the walk `[0,2,4]` is noncrossing
and reclosing its side gives a torus (`NoncrossingClosedWalkEuler`).  Its passages, the chords from
the reversal `alpha d` of a walk dart to its successor `next d`, are `{1,2}`, `{3,4}` and `{5,0}` at
the one vertex, and they interleave in rotation order.

* `RotationBetween M x y z`: rotating from `x`, the dart `z` comes before `y`.
* `PassagesNoninterleaving M w`: for two distinct positions `i`, `j` of the walk at one vertex, the
  endpoints `alpha w[j]` and `w[j+1]` of the second passage are both inside the sector of the first
  passage, or both outside it.  Positions are stated with `finRotate`, so no decidable equality on
  darts is needed.
* `IsNoncrossingClosedWalk.eulers_of_vertexCount_le`: the Euler equalities from the vertex bound.
* `NoninterleavingVertexCountStatement` (named residual, not proved here): a noncrossing closed walk
  whose passages do not interleave has the vertex bound.  At a vertex, `k` non-crossing chords cut the
  rotation into `k + 1` sectors shared between the two reclosings.
* `IsNoncrossingClosedWalk.eulers_of_noninterleaving`: both Euler equalities from the residual.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u

/-- **A dart inside a rotation sector.**  Rotating from `x`, the dart `z` is reached after at least
one step and before `y`. -/
def RotationBetween (M : CombMap.{u}) (x y z : M.Dart) : Prop :=
  ∃ a : ℕ, 0 < a ∧ (M.sigma ^ a) x = z ∧ ∀ b, 0 < b → b ≤ a → (M.sigma ^ b) x ≠ y

/-- **The passages of a walk do not interleave.**  The passage at position `i` is the chord from the
reversal `alpha w[i]` of the walk dart to the walk dart `w[i+1]` after it (cyclically), at the vertex
where `w[i]` ends.  For distinct positions `i`, `j` at one vertex, the endpoints of the passage at `j`
lie both inside the sector of the passage at `i` or both outside it. -/
def PassagesNoninterleaving (M : CombMap.{u}) (w : List M.Dart) : Prop :=
  ∀ i j : Fin w.length, i ≠ j →
    M.vertexOf (M.alpha (w.get i)) = M.vertexOf (M.alpha (w.get j)) →
      (RotationBetween M (M.alpha (w.get i)) (w.get (finRotate w.length i)) (M.alpha (w.get j)) ↔
        RotationBetween M (M.alpha (w.get i)) (w.get (finRotate w.length i))
          (w.get (finRotate w.length j)))

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Both reclosings keep the Euler characteristic once they have enough vertices.**  If the two
reclosings of a noncrossing closed walk `w` in a planar map together have at least `|w|` more
vertices than the map, both keep its Euler characteristic: together they have `|w|` more edges and
two more faces, and each is connected, so each Euler characteristic is at most two. -/
theorem eulers_of_vertexCount_le (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hV : M.vertexCount + w.length ≤
      (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).vertexCount +
        (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).vertexCount) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic ∧
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic := by
  have hE := hw.edgeCount_add hM
  have hF := hw.faceCount_add hM
  have h1 := (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic_le_two
    (reclosedMap_connected M (sideFaces M w) (hw.innerCycle hM) hM.1)
  have h2 := (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic_le_two
    (reclosedMap_connected M (sideOutside M w) (hw.outerCycle hM) hM.1)
  have h3 := hM.2
  unfold CombMap.eulerCharacteristic at h1 h2 h3 ⊢
  constructor <;> omega

end IsNoncrossingClosedWalk

/-- **The vertex bound for a noncrossing walk whose passages do not interleave** (named residual).
For a noncrossing closed walk in a planar map whose passages do not interleave, the two reclosings
together have at least `|w|` more vertices than the map. -/
def NoninterleavingVertexCountStatement : Prop :=
  ∀ (M : CombMap.{u}) (hM : M.IsPlanar) (w : List M.Dart) (hw : IsNoncrossingClosedWalk M w),
    PassagesNoninterleaving M w →
      M.vertexCount + w.length ≤
        (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).vertexCount +
          (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).vertexCount

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Both reclosings of a noncrossing closed walk whose passages do not interleave keep the Euler
characteristic**, from the named vertex bound. -/
theorem eulers_of_noninterleaving (hcount : NoninterleavingVertexCountStatement.{u})
    (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (hni : PassagesNoninterleaving M w) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic ∧
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic :=
  hw.eulers_of_vertexCount_le hM (hcount M hM w hw hni)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.RotationBetween
#audit_axioms GroupApproximation.GGT.VanKampen.PassagesNoninterleaving
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.eulers_of_vertexCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.NoninterleavingVertexCountStatement
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.eulers_of_noninterleaving
