import GroupApproximation.Manuscript.NonMF.Full.GL06p.SlitCore
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e: the slit pocket core with slack `κ` in the slit minimality

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

`GL06p.SlitPocketCore` asks both slit sides to be metrically class-minimal
(`GL06p.MetricClassMinimal`): no longer than the class minimum `m`.

**The exact statement is not known to be false.** The planned construction is a G-face strip
(`GGT.VanKampen.PathStrip`, lane pal-envelope). In it, the complement between the two slits holds
no relator cell, so walk values there depend only on endpoints. With `follows` and a nonempty arc,
the two slits then end at two distinct vertices of `Π`. When the nearest cell attains `m` at a
single vertex, one slit has norm up to `m + 2`. Pockets whose complement between the slits holds
other relator cells are not excluded by this argument.

This module states the weakening that the strip design needs, under a new name:

* `SlitPocketCoreSlack D κ Δ`: `SlitPocketCore` with each slit length at most `m + κ`, spelled
  `MetricClassMinimal D Δ (slit.length - κ)`.
* `SlitPocketCoreSlack.ofCore`: every exact core is a slack core, so this is a weakening.
* `SlitPocketCoreSlack.toCore`: at `κ = 0` it is the exact core.
* `slitPocketCoreSlackStatement κ`, with `slitPocketCoreSlackStatement_of_core` and
  `slitPocketCoreStatement_of_slack_zero`.

Satisfiability check (by hand, on the board of nm-gl06e): take `∂Δ` and `∂Π` simple and disjoint,
and the minimizer's interior off both. The strip's pocket walk is simple, with slit norms `≤ m + 2`
and `m`, so it gives a slack core with `κ = 2`. This has not been checked in Lean. The windows argument
(`GL06p/Windows`) needs `ε ≥ κ` to absorb the slack, since `NearWindow`'s bound is `ε + ε`; that
re-proof belongs to the owners of GL06p.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06eSlit

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

section Slack

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Class-minimality is downward closed. -/
theorem metricClassMinimal_mono {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    {m n : ℕ} (h : GL06p.MetricClassMinimal D Delta m) (hnm : n ≤ m) :
    GL06p.MetricClassMinimal D Delta n :=
  fun Y hY j q hq => le_trans hnm (h Y hY j q hq)

/-- **The slit pocket core with slack `κ`** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the fields of `GL06p.SlitPocketCore`, with each slit side at most
`κ` longer than the class minimum. -/
structure SlitPocketCoreSlack (D : RelGenSet G Lambda) (κ : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    where
  copy : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta copy
  pocket : PocketRegion copy
  follows : pocket.outer.FollowsBoundary
  inner : RelatorCell copy.toCombMap copy.outerFace W
  inner_mem : inner ∈ copy.relatorCells
  inner_face : inner.face ∈ pocket.faces
  nearest : Fin copy.rCellCount
  nearest_face : (cell copy nearest).face ∉ pocket.faces
  arc : CyclicArc (cellDarts copy nearest)
  outerPart : List copy.toCombMap.Dart
  slitIn : List copy.toCombMap.Dart
  slitOut : List copy.toCombMap.Dart
  decomposition : invDarts copy pocket.outer.cycle =
    outerPart ++ slitIn ++ invDarts copy arc.darts ++ slitOut
  outer_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy outerPart)) (dartWord copy outerPart)
  slitIn_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy slitIn)) (dartWord copy slitIn)
  slitOut_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy slitOut)) (dartWord copy slitOut)
  outer_length_le : outerPart.length ≤ Delta.boundaryWord.length
  /-- The slit side `s₁` is at most `κ` longer than every class walk from the boundary to a cell. -/
  slitIn_minimal : GL06p.MetricClassMinimal D Delta (slitIn.length - κ)
  /-- The slit side `s₂` is at most `κ` longer than every class walk from the boundary to a cell. -/
  slitOut_minimal : GL06p.MetricClassMinimal D Delta (slitOut.length - κ)
  foot_in : ∀ d ∈ slitIn.head?, ∃ b : copy.toCombMap.Dart,
    copy.toCombMap.faceOf b = copy.outerFace ∧ copy.toCombMap.vertexOf b = copy.toCombMap.vertexOf d
  foot_out : ∀ d ∈ slitOut.getLast?, ∃ b : copy.toCombMap.Dart,
    copy.toCombMap.faceOf b = copy.outerFace ∧
      copy.toCombMap.vertexOf b = copy.toCombMap.vertexOf (copy.toCombMap.alpha d)

namespace SlitPocketCoreSlack

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}

/-- **An exact core is a slack core**, for every `κ`. -/
def ofCore (κ : ℕ) (C : GL06p.SlitPocketCore D Delta) : SlitPocketCoreSlack D κ Delta where
  copy := C.copy
  equiv := C.equiv
  pocket := C.pocket
  follows := C.follows
  inner := C.inner
  inner_mem := C.inner_mem
  inner_face := C.inner_face
  nearest := C.nearest
  nearest_face := C.nearest_face
  arc := C.arc
  outerPart := C.outerPart
  slitIn := C.slitIn
  slitOut := C.slitOut
  decomposition := C.decomposition
  outer_geodesic := C.outer_geodesic
  slitIn_geodesic := C.slitIn_geodesic
  slitOut_geodesic := C.slitOut_geodesic
  outer_length_le := C.outer_length_le
  slitIn_minimal := metricClassMinimal_mono C.slitIn_minimal (Nat.sub_le _ _)
  slitOut_minimal := metricClassMinimal_mono C.slitOut_minimal (Nat.sub_le _ _)
  foot_in := C.foot_in
  foot_out := C.foot_out

/-- **A slack core with `κ = 0` is an exact core.** -/
def toCore (C : SlitPocketCoreSlack D 0 Delta) : GL06p.SlitPocketCore D Delta where
  copy := C.copy
  equiv := C.equiv
  pocket := C.pocket
  follows := C.follows
  inner := C.inner
  inner_mem := C.inner_mem
  inner_face := C.inner_face
  nearest := C.nearest
  nearest_face := C.nearest_face
  arc := C.arc
  outerPart := C.outerPart
  slitIn := C.slitIn
  slitOut := C.slitOut
  decomposition := C.decomposition
  outer_geodesic := C.outer_geodesic
  slitIn_geodesic := C.slitIn_geodesic
  slitOut_geodesic := C.slitOut_geodesic
  outer_length_le := C.outer_length_le
  slitIn_minimal := by simpa using C.slitIn_minimal
  slitOut_minimal := by simpa using C.slitOut_minimal
  foot_in := C.foot_in
  foot_out := C.foot_out

end SlitPocketCoreSlack

end Slack

/-- **Slack slit pocket cores exist** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): `GL06p.slitPocketCoreStatement` with slack `κ` in the slit
minimality.  Not proved here. -/
def slitPocketCoreSlackStatement (κ : ℕ) : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        GL06p.MetricNearestWalk D Delta → Nonempty (SlitPocketCoreSlack D κ Delta)

/-- The exact statement gives the slack statement for every `κ`. -/
theorem slitPocketCoreSlackStatement_of_core (κ : ℕ)
    (h : GL06p.slitPocketCoreStatement.{u, w, v}) : slitPocketCoreSlackStatement.{u, w, v} κ := by
  intro _G _ _Lambda D W Delta hlea hletters hW hcells hwalk
  obtain ⟨C⟩ := h D W Delta hlea hletters hW hcells hwalk
  exact ⟨SlitPocketCoreSlack.ofCore κ C⟩

/-- The slack statement at `κ = 0` gives the exact statement. -/
theorem slitPocketCoreStatement_of_slack_zero (h : slitPocketCoreSlackStatement.{u, w, v} 0) :
    GL06p.slitPocketCoreStatement.{u, w, v} := by
  intro _G _ _Lambda D W Delta hlea hletters hW hcells hwalk
  obtain ⟨C⟩ := h D W Delta hlea hletters hW hcells hwalk
  exact ⟨C.toCore⟩

end GroupApproximation.Full.GL06eSlit

#audit_axioms GroupApproximation.Full.GL06eSlit.metricClassMinimal_mono
#audit_axioms GroupApproximation.Full.GL06eSlit.SlitPocketCoreSlack.ofCore
#audit_axioms GroupApproximation.Full.GL06eSlit.SlitPocketCoreSlack.toCore
#audit_axioms GroupApproximation.Full.GL06eSlit.slitPocketCoreSlackStatement_of_core
#audit_axioms GroupApproximation.Full.GL06eSlit.slitPocketCoreStatement_of_slack_zero
