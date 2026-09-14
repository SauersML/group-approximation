import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMapHolds
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: direct object steps of the polygons

A polygon of `OsinLemma94RealizedPolygons` makes a *direct object step* at side `s` when side `s`
runs along an object `o` (a relator cell or the exterior) and the next side that is not a cutting
path runs along a different object `o′`, with only cutting paths between.  Such a step sits at a
corner where the two objects touch.

* `OsinLemma94RealizedPolygons.IsDirectStep`, `directSteps`: the steps of one polygon.
* `OsinLemma94ObjectTouchComponentsInput` (open): under the binders of
  `OsinLemma94ContactMapEmptyTwoGonInput`, the direct steps of all polygons number at most `K n`.

The input is the charge target of the empty nondegenerate small faces of the contact map that hold
no selected region (`Estimating/OsinLemma94ContactEmptyTwoGon.lean`).  It does not go through
`OsinLemma94ContactTransitionInput`, which the contact map is itself building toward.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **A direct object step of polygon `k` at side `s`**: side `s` runs along an object `o`, the
next side that is not a cutting path runs along a different object `o′`, and only cutting paths
lie between. -/
def IsDirectStep (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) : Prop :=
  ∃ o o' : Option (Fin S.diagram.rCellCount), o ≠ o' ∧ sideObject (P.kind k s) = some o ∧
    ∃ t, 0 < t ∧ t < P.sideCount k ∧
      sideObject (P.kind k ((s + t) % P.sideCount k)) = some o' ∧
        ∀ i, 0 < i → i < t → P.kind k ((s + i) % P.sideCount k) = .cutting

/-- The direct object steps of polygon `k`. -/
noncomputable def directSteps (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) : Finset ℕ :=
  (Finset.range (P.sideCount k)).filter fun s => P.IsDirectStep k s

end OsinLemma94RealizedPolygons

/-- **The direct object steps of Lemma 9.4** (open).  Under the binders of
`OsinLemma94ContactMapEmptyTwoGonInput`, the direct object steps of all polygons number at most
`K n`.

Model tests (hand).
* No polygons: the sum is empty.
* Two relator cells meeting at one vertex, with a polygon on each side of the meeting point: each
  polygon reads one cell side and then the other, so two direct steps at one touch point.
* Two cells meeting at `m` points bound `m - 1` bubbles, each with two direct steps.  An unpinched
  bubble with two nonempty arcs is a singleton contiguity region, and `false_of_avoided_singleton`
  excludes it on a globally distinguished family; a pinched one is merged by the split of the
  pinch.  Without these exclusions the count grows with `m` at fixed `n`. -/
def OsinLemma94ObjectTouchComponentsInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∑ k, (P.directSteps k).card ≤ K * Delta.rCellCount

end GroupApproximation.GGT.VanKampen
