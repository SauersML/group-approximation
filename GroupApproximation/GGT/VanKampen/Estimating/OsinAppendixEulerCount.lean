import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerHereditary
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler count input of Lemma 9.7

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(a).  `EulerCountInput`
(`Estimating/OsinAppendixSectionInduction.lean`) asks, at a least-area diagram and a distinguished
system without loops or multiple edges, for two counts: the Euler count `|M| ≤ 3(n + r − 1)` of
`Φ'_M`, and the endpoint-closed planar edge bound of `Φ_M`.

* `GloballyDistinguishedSectionFamily.hasEndpointClosedPlanarEdgeBound`: the planar edge bound of
  `Φ_M`.  No relator cell lies on the faces of a selected region, since a relator cell reading a
  trivial word contradicts least area (`ContiguityGeometry.innerGRegion`), so
  `hasEndpointClosedPlanarEdgeBound_of_phiData` applies.
* `PhiPrimeCountInput`: the Euler count of `Φ'_M`, the remaining input.
* `eulerCountInput_of_phiPrimeCount`: `EulerCountInput` from `PhiPrimeCountInput`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The planar edge bound of `Φ_M` at a distinguished system** without loops or multiple
edges, at least area. -/
theorem GloballyDistinguishedSectionFamily.hasEndpointClosedPlanarEdgeBound
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hlea : Delta.LeastArea)
    (hloops : S.NoLoops) (hmulti : S.NoMultipleEdges)
    [DecidableEq (RegionCandidate.InteriorEdge S.family)]
    [DecidableRel (RegionCandidate.InteriorEdge.Incident (selected := S.family))] :
    HasEndpointClosedPlanarEdgeBound
      (RegionCandidate.InteriorEdge.Incident (selected := S.family)) := by
  have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
  exact RegionCandidate.hasEndpointClosedPlanarEdgeBound_of_phiData S.pairwise
    (fun a _ i => (a.2.innerGRegion hleaS).cells_avoid _ (cell_mem S.diagram i))
    S.nondegenerate hloops hmulti

/-- **The Euler count of `Φ'_M`** (G3), from the proof of Osin's Lemma 9.7(a): at a least-area
diagram with `n` relator cells and `r` sections, a distinguished system without loops or multiple
edges has at most `3(n + r − 1)` regions.  The vertices of `Φ'_M` are the cells and the sections,
and its edges are the selected regions.  A producer also needs the two-gon half of `(∗)`: two
regions of one cell to one section merge when no relator cell lies between them, against
`card_minimal`. -/
def PhiPrimeCountInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → 0 < Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        S.NoLoops → S.NoMultipleEdges →
          S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)

/-- **`EulerCountInput` from the Euler count of `Φ'_M`.**  The planar edge bound of `Φ_M` is
`GloballyDistinguishedSectionFamily.hasEndpointClosedPlanarEdgeBound`. -/
theorem eulerCountInput_of_phiPrimeCount {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    (hcount : PhiPrimeCountInput.{u, w, v} D lambda c eps W) :
    EulerCountInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea hcells S hloops hmulti
  classical
  refine ⟨hcount Delta cuts hlea hcells S hloops hmulti, ?_⟩
  convert S.hasEndpointClosedPlanarEdgeBound hlea hloops hmulti

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.hasEndpointClosedPlanarEdgeBound
#audit_axioms GroupApproximation.GGT.VanKampen.eulerCountInput_of_phiPrimeCount
