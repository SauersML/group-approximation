import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: boundary cycles of face sets are vertex chains

Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), lane gl-p07-02 (first half).  The connectivity lane gl-p07-01
(`keepUnion_connected`, `unionMap_connected`) needs the boundary cycles of the regions `a`, `b`
as walks chained at vertices: `c.IsChain fun d e => vertexOf (α d) = vertexOf e`.

## The mathematical proof

Let `F` be a `FaceSetBoundary` of a face set.  Consecutive cycle darts `d, e` satisfy
`BoundaryStep d e`: `e` is reached from `φ d` by internal moves `x ↦ φ (α x)`, with
`φ = σ * α` the face permutation.

1. `φ d = σ (α d)` starts at the vertex of `α d`, i.e. where `d` ends.
2. An internal move `x ↦ φ (α x) = σ (α (α x)) = σ x` stays at the vertex of `x`.
3. Hence every dart reached from `φ d` by internal moves, in particular `e`, starts where `d`
   ends: `vertexOf (α d) = vertexOf e`.

Applying this to `cycle_chain` gives the chain, and to `cycle_closes` the closing step.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Step 1.**  The face successor of a dart starts where the dart ends. -/
theorem regionTouch_vertexOf_facePerm (M : CombMap.{v}) (d : M.Dart) :
    M.vertexOf (M.facePerm d) = M.vertexOf (M.alpha d) := by
  rw [show M.facePerm d = M.sigma (M.alpha d) from rfl]
  exact M.vertexOf_sigma (M.alpha d)

/-- **Step 2.**  Internal boundary moves stay at one vertex. -/
theorem regionTouch_vertexOf_of_reflTransGen {X : DiscDiagram.{u, w, v} W}
    {faces : Finset X.toCombMap.Face} {x e : X.toCombMap.Dart}
    (h : Relation.ReflTransGen (InternalBoundaryMove X faces) x e) :
    X.toCombMap.vertexOf e = X.toCombMap.vertexOf x := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    obtain ⟨-, -, hc⟩ := hbc
    rw [hc, regionTouch_vertexOf_facePerm, X.toCombMap.alpha_involutive _]
    exact ih

/-- **Step 3.**  A boundary step is a vertex step: the next boundary dart starts where the
current one ends. -/
theorem regionTouch_vertexStep_of_boundaryStep {X : DiscDiagram.{u, w, v} W}
    {faces : Finset X.toCombMap.Face} {d e : X.toCombMap.Dart}
    (h : BoundaryStep X faces d e) :
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  rw [regionTouch_vertexOf_of_reflTransGen h.2.2, regionTouch_vertexOf_facePerm]

/-- **The boundary cycle of a face set is chained at vertices.** -/
theorem regionTouch_cycle_isChain {X : DiscDiagram.{u, w, v} W}
    {faces : Finset X.toCombMap.Face} (F : FaceSetBoundary X faces) :
    F.cycle.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e :=
  F.cycle_chain.imp fun _ _ h => regionTouch_vertexStep_of_boundaryStep h

/-- **The boundary cycle of a face set closes at a vertex.** -/
theorem regionTouch_cycle_closes {X : DiscDiagram.{u, w, v} W}
    {faces : Finset X.toCombMap.Face} (F : FaceSetBoundary X faces) :
    X.toCombMap.vertexOf (X.toCombMap.alpha (F.cycle.getLast F.cycle_nonempty)) =
      X.toCombMap.vertexOf (F.cycle.head F.cycle_nonempty) :=
  regionTouch_vertexStep_of_boundaryStep F.cycle_closes

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_vertexOf_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_vertexOf_of_reflTransGen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_vertexStep_of_boundaryStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_cycle_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_cycle_closes
