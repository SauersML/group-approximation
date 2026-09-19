import GroupApproximation.Analysis.STW22AntipodalTraceBoundary
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Countability and metrizability of the antipodal trace boundary

The finite part of the boundary is a countable topological sum of compact
real-projective spaces.  A countable basis for its one-point compactification
consists of the images of a countable basis of the finite part together with
the complements of finite unions of components.  This file carries out that
argument explicitly and then applies Urysohn metrization.
-/

namespace GroupApproximation
namespace STW22AntipodalTraceBoundaryTopology

open Set TopologicalSpace
open STW22
open STW22AntipodalTraceBoundary
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

private abbrev FiniteBoundary : Type :=
  Σ n : ℕ, RP (antipodalBlockDimension n)

/-- The union of a finite set of connected components of the finite boundary. -/
private def finiteComponentUnion (s : Finset ℕ) : Set FiniteBoundary :=
  ⋃ n ∈ s, Set.range (@Sigma.mk ℕ
    (fun n ↦ RP (antipodalBlockDimension n)) n)

private theorem isOpen_finiteComponentUnion (s : Finset ℕ) :
    IsOpen (finiteComponentUnion s) := by
  exact isOpen_biUnion fun n _ ↦ isOpen_range_sigmaMk

private theorem isCompact_finiteComponentUnion (s : Finset ℕ) :
    IsCompact (finiteComponentUnion s) := by
  exact s.isCompact_biUnion fun n _ ↦ isCompact_range continuous_sigmaMk

/-- A concrete countable basis for the one-point boundary: ordinary basis
sets in its finite open part, and complements of finite component unions at
infinity. -/
private def boundaryBasis : Set (Set AntipodalTraceBoundary) :=
  ((fun U : Set FiniteBoundary ↦
      ((↑) : FiniteBoundary → AntipodalTraceBoundary) '' U) ''
      TopologicalSpace.countableBasis FiniteBoundary) ∪
    Set.range (fun s : Finset ℕ ↦
      (((↑) : FiniteBoundary → AntipodalTraceBoundary) ''
        finiteComponentUnion s)ᶜ)

private theorem boundaryBasis_countable : boundaryBasis.Countable := by
  exact (TopologicalSpace.countable_countableBasis FiniteBoundary).image _ |>.union
    (Set.countable_range _)

private theorem boundaryBasis_isTopologicalBasis :
    IsTopologicalBasis boundaryBasis := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    rcases hU with hU | hU
    · obtain ⟨V, hVB, rfl⟩ := hU
      exact OnePoint.isOpen_image_coe.mpr
        (TopologicalSpace.isOpen_of_mem_countableBasis hVB)
    · obtain ⟨s, rfl⟩ := hU
      exact OnePoint.isOpen_compl_image_coe.mpr
        ⟨(isCompact_finiteComponentUnion s).isClosed,
          isCompact_finiteComponentUnion s⟩
  · intro x U hxU hU
    induction x using OnePoint.rec with
    | infty =>
        have hcompact : IsCompact
            ((((↑) : FiniteBoundary → AntipodalTraceBoundary) ⁻¹' U)ᶜ) :=
          (OnePoint.isOpen_iff_of_mem hxU).mp hU |>.2
        obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
          (fun n : ℕ ↦ Set.range (@Sigma.mk ℕ
            (fun n ↦ RP (antipodalBlockDimension n)) n))
          (fun _ ↦ isOpen_range_sigmaMk) (by
            intro y _
            rcases y with ⟨n, y⟩
            exact Set.mem_iUnion.mpr ⟨n, ⟨y, rfl⟩⟩)
        refine ⟨(((↑) : FiniteBoundary → AntipodalTraceBoundary) ''
            finiteComponentUnion s)ᶜ, ?_, ?_, ?_⟩
        · exact Or.inr ⟨s, rfl⟩
        · exact Set.mem_compl (OnePoint.infty_notMem_image_coe)
        · intro y hy
          induction y using OnePoint.rec with
          | infty => exact hxU
          | coe y =>
              by_contra hyU
              have hyc : y ∈
                  ((((↑) : FiniteBoundary → AntipodalTraceBoundary) ⁻¹' U)ᶜ) :=
                hyU
              have hys : y ∈ finiteComponentUnion s := hs hyc
              exact hy ⟨y, hys, rfl⟩
    | coe x =>
        have hxpre : x ∈
            ((↑) : FiniteBoundary → AntipodalTraceBoundary) ⁻¹' U := hxU
        have hopenpre : IsOpen
            (((↑) : FiniteBoundary → AntipodalTraceBoundary) ⁻¹' U) :=
          hU.preimage OnePoint.continuous_coe
        obtain ⟨V, hVB, hxV, hVsub⟩ :=
          (TopologicalSpace.isBasis_countableBasis FiniteBoundary).exists_subset_of_mem_open
            hxpre hopenpre
        refine ⟨((↑) : FiniteBoundary → AntipodalTraceBoundary) '' V,
          Or.inl ⟨V, hVB, rfl⟩, ⟨x, hxV, rfl⟩, ?_⟩
        rintro _ ⟨y, hyV, rfl⟩
        exact hVsub hyV

/-- The literal compact extreme-boundary candidate is second countable. -/
instance antipodalTraceBoundary_secondCountableTopology :
    SecondCountableTopology AntipodalTraceBoundary :=
  boundaryBasis_isTopologicalBasis.secondCountableTopology boundaryBasis_countable

/-- The literal boundary is metrizable (and already compact Hausdorff). -/
instance antipodalTraceBoundary_metrizableSpace :
    MetrizableSpace AntipodalTraceBoundary := by infer_instance

/-- Binder-free package of the exact boundary regularity used by the Bauer
trace-simplex endpoint. -/
theorem antipodalTraceBoundary_compact_metrizable :
    CompactSpace AntipodalTraceBoundary ∧
      SecondCountableTopology AntipodalTraceBoundary ∧
      MetrizableSpace AntipodalTraceBoundary ∧
      T2Space AntipodalTraceBoundary :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

#audit_closed_axioms antipodalTraceBoundary_compact_metrizable

end

end STW22AntipodalTraceBoundaryTopology
end GroupApproximation
