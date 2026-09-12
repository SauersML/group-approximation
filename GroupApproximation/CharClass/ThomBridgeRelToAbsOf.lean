import GroupApproximation.CharClass.ThomBridgeRelToAbs
import GroupApproximation.CharClass.ThomBridgeTotalNaturalOf
import GroupApproximation.CharClass.RelativeSubspaceIsoOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom bridge over a field commutes with `relToAbs`

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomBridgeRelToAbs.relToAbs_bridgeTotal` shows at `F₂` that the absolute image of a class
of the vector-bundle pair is the chart restriction of the absolute image of the class it
becomes on the projectivisation pair.  It is two applications of `relToAbs_naturality`, one
along the chart inclusion and one along the identity of `P(p ⊕ 1)`.  Over a field `K` the
chart step is `bridgeChartOf_hom_eq`, and the identity step is `absPull_id_applyOf`.

## Main declarations

* `relToAbs_bridgeTotalOf` — **the bridge over a field commutes with `relToAbs`**.
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace GroupApproximation.CharClass

noncomputable section

open ThomChernDeg RelativeSupport

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The bridge over a field commutes with `relToAbs`.** -/
theorem relToAbs_bridgeTotalOf (K : Type) [Field K] [CompactSpace X] [T2Space X]
    (p : Bundle X ι) (n : ℕ)
    (u : ↥(relCohomology K (TopCat.of (Bundle.Total p))
      ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)) :
    (relToAbs K (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n).hom u
      = pull (cmap (bridgeChartIncl p)) n
          ((relToAbs K (TopCat.of (Bundle.Proj p.plusOne))
            (Set.range (Bundle.projIncl p)) n).hom (bridgeTotalOf K p n u)) := by
  have hA : ∀ v ∈ ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹'
        Bundle.puncturedSet p),
      (ConcreteCategory.hom (cmap (bridgeChartIncl p))) v
        ∈ ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)) := by
    intro v hv
    have hmem : (((Bundle.chartOpensHomeoTotal p)
        ((Bundle.chartOpensHomeoTotal p).symm v) : Bundle.Total p) : X × (ι → ℂ))
        ∈ Bundle.puncturedSet p := by
      rw [(Bundle.chartOpensHomeoTotal p).apply_symm_apply]
      exact hv
    exact (Bundle.chartOpensHomeoTotal_mem_puncturedSet p
      ((Bundle.chartOpensHomeoTotal p).symm v)).mp hmem
  have hid := (bridgeChartOf K p n).inv_hom_id
  have hu : ((bridgeChartOf K p n).hom).hom ((bridgeChartOf K p n).inv.hom u) = u := by
    have h := congrArg (fun t => t.hom u) hid
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_id, LinearMap.id_coe, id_eq] at h
    exact h
  -- square one: the chart inclusion
  have hsq1 := relToAbs_naturality K (cmap (bridgeChartIncl p)) hA n
  have hnat1 := congrArg (fun t => t.hom ((bridgeChartOf K p n).inv.hom u)) hsq1
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hnat1
  rw [bridgeChartOf_hom_eq K p n hA] at hu
  rw [hu] at hnat1
  -- square two: the identity of `P(p ⊕ 1)`, shrinking the subspace
  have hsq2 := relToAbs_naturality K (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
    (A := (Set.range (Bundle.projIncl p) : Set ↥(TopCat.of (Bundle.Proj p.plusOne))))
    (B := ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
      : Set (Bundle.Proj p.plusOne)))
    (fun _ hx => range_projIncl_subset_notZero p hx) n
  have hnat2 := congrArg (fun t => t.hom ((bridgeChartOf K p n).inv.hom u)) hsq2
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    absPull_id_applyOf] at hnat2
  rw [hnat2] at hnat1
  show _ = (absPullOf K (cmap (bridgeChartIncl p)) n).hom _
  rw [bridgeTotalOf_apply]
  exact hnat1.symm

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms relToAbs_bridgeTotalOf

end

end GroupApproximation.CharClass
