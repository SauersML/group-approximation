import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLeastAreaCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge cut from a region cut of an O-equivalent copy

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a).  The two selected regions
between the cells `Π_1` and `Π_2` live on the optimal diagram of a globally
distinguished family, an O-equivalent copy `Δ'` of `Δ`.  The subdiagram `Ξ` they cut
out is the piece of a region cut of `Δ'`, with `∂Ξ = s_1 t_1 s_2 t_2`.

* `OsinMultipleEdgeCut.ofRegionCut`: take a region cut of an O-equivalent copy of a
  least-area `Δ` that keeps at least one relator cell. Suppose its inverse boundary
  walk splits as `s_1 t_1 s_2 t_2` into quasi-geodesic parts, the sides `s_1`, `s_2`
  are no longer than `ε`, and regions to `t_1`, `t_2` glue back into `Δ'`. Then the
  cut is an `OsinMultipleEdgeCut` of `Δ`. Least area and the relator count pass
  along the O-equivalence, and the transport composes with it.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **The multiple-edge cut from a region cut** (input G2 of lane `hull-select`,
assembly).  Let `Δ` be least area and `Δ'` an O-equivalent copy, such as the optimal
diagram of a globally distinguished family. Take a region cut of `Δ'` that keeps at
least one relator cell, with its inverse boundary walk split as `s_1 t_1 s_2 t_2`
into parts with `(λ, c)`-quasi-geodesic words and the sides `s_1`, `s_2` no longer
than `ε`. The cut is a cut of `Δ` as soon as regions to `t_1` and `t_2` in
O-equivalent copies of the piece glue back into cell-to-cell regions of O-equivalent
copies of `Δ'`. -/
noncomputable def OsinMultipleEdgeCut.ofRegionCut {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {Delta Delta' : DiscDiagram.{u, w, v} W}
    (equiv : OEquivalentDiscDiagram Delta Delta') (hlea : Delta.LeastArea)
    (cut : Surgery.MapCollapse.RegionCutData Delta') (hcells : 0 < cut.cells.length)
    (s₁ t₁ s₂ t₂ : List Delta'.toCombMap.Dart)
    (hdecomposition : Embedded.invDarts Delta' cut.region.toBoundaryCycle.cycle =
      s₁ ++ t₁ ++ s₂ ++ t₂)
    (hquasi : ∀ part ∈ [s₁, t₁, s₂, t₂],
      IsLambdaCQuasiGeodesicWord D lambda c (Embedded.dartWord Delta' part))
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (htransport :
      ∀ j : Fin (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi).count,
        ((j : ℕ) = 1 ∨ (j : ℕ) = 3) →
          ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram cut.diagram Xi →
            ∀ a : RegionCandidate D eps Xi,
              RegionCandidate.TargetsSectionIndex
                  (cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi) j a →
                ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
                  (t : Fin Y.rCellCount),
                  Nonempty (OEquivalentDiscDiagram Delta' Y) ∧
                    b.2.target = some t ∧ b.2.source ≠ t ∧
                    b.contiguityDegree = a.contiguityDegree) :
    OsinMultipleEdgeCut D lambda c eps Delta :=
  have key := cut.fourSectionCuts_leastAreaCut D lambda c eps (equiv.leastArea hlea) hcells
    s₁ t₁ s₂ t₂ hdecomposition hquasi hs₁ hs₂
  { enclosed := cut.diagram
    leastArea := key.1
    rCellCount_pos := key.2.1
    rCellCount_lt := lt_of_lt_of_eq key.2.2.1 equiv.rCellCount_eq
    sections := cut.fourSectionCuts D lambda c s₁ t₁ s₂ t₂ hdecomposition hquasi
    count_eq := key.2.2.2.1
    side_short := key.2.2.2.2
    transport := by
      intro j hj Xi E a ha
      obtain ⟨Y, b, t, ⟨EY⟩, htarget, hne, hdeg⟩ := htransport j hj Xi E a ha
      exact ⟨Y, b, t, ⟨equiv.trans EY⟩, htarget, hne, hdeg⟩ }

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCut.ofRegionCut
