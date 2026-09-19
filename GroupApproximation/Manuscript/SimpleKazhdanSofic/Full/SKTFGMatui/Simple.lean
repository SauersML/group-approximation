import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.FullGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiSimplicity
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerPerm
import GroupApproximation.Meta.AxiomGuard

/-!
# Matui's theorem for `[[T]]'` as homeomorphisms (census row `3eaee0a2dc7e`)

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

The repository has two encodings of the topological full group `[[T]]`: `topologicalFullGroup T`,
a subgroup of the homeomorphism group (`FlipConverse.FullGroup`, used for the flip converse), and
`fullGroup T`, a subgroup of the permutation group (`Full.StepanovMatui.Matui`).  The StepanovMatui
lane proved Matui's theorem for the second
(`Full.StepanovMatui.Matui.isSimpleGroup_commutator_fullGroup`, with Lemma 3.4 as
`alternatingFullGroup_le_of_ne_bot`; the printed remark is `printedMatuiRemark`).  This file moves
it to the first.

* `map_topologicalFullGroup`: on a compact Hausdorff space, forgetting continuity
  (`homeoToPerm`) maps `topologicalFullGroup T` onto `fullGroup T`.  An element of `fullGroup T`
  is continuous, and by compactness so is its inverse, so it is a homeomorphism.
* `map_derivedTopologicalFullGroup`, `derivedTopologicalFullGroupMulEquiv`: hence
  `⁅[[T]], [[T]]⁆` as homeomorphisms is isomorphic to `⁅fullGroup T, fullGroup T⁆`, because
  `homeoToPerm` is injective and maps commutator subgroups to commutator subgroups.
* `isSimpleGroup_derivedTopologicalFullGroup`: `⁅[[T]], [[T]]⁆` is simple for a minimal
  homeomorphism of an infinite compact Hausdorff totally separated space.
* `printedMatuiCantorMinimal`: the closed statement for Cantor minimal systems.  A Cantor minimal
  system is compact, metrizable (so Hausdorff), totally disconnected (so totally separated, having a
  clopen basis) and perfect and nonempty (so infinite).
-/

namespace GroupApproximation.Full.SKTFGMatui

open GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
open GroupApproximation.Full.StepanovMatui.Matui
open scoped commutatorElement

universe u

section Transport

variable {X : Type*} [TopologicalSpace X]

theorem homeoToPerm_injective : Function.Injective (homeoToPerm (X := X)) :=
  fun _ _ h => Homeomorph.toEquiv_injective h

/-- On a compact Hausdorff space, forgetting continuity maps `[[T]]` (homeomorphisms) onto
`[[T]]` (permutations). -/
theorem map_topologicalFullGroup [CompactSpace X] [T2Space X] (T : X ≃ₜ X) :
    (topologicalFullGroup T).map homeoToPerm = fullGroup T := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨n, hn, hhn⟩ := mem_topologicalFullGroup.1 hh
    exact mem_fullGroup.2 ⟨n, hn, fun x => hhn x⟩
  · intro hg
    have hg' : IsFullGroupElement T g := mem_fullGroup.1 hg
    obtain ⟨n, hn, hgn⟩ := mem_fullGroup.1 hg
    refine ⟨{ toEquiv := g
              continuous_toFun := hg'.continuous
              continuous_invFun := (IsFullGroupElement.inv hg').continuous }, ?_, rfl⟩
    exact mem_topologicalFullGroup.2 ⟨n, hn, fun x => hgn x⟩

/-- Forgetting continuity maps `⁅[[T]], [[T]]⁆` onto `⁅fullGroup T, fullGroup T⁆`. -/
theorem map_derivedTopologicalFullGroup [CompactSpace X] [T2Space X] (T : X ≃ₜ X) :
    (⁅topologicalFullGroup T, topologicalFullGroup T⁆ : Subgroup (X ≃ₜ X)).map homeoToPerm =
      ⁅fullGroup T, fullGroup T⁆ := by
  rw [Subgroup.map_commutator, map_topologicalFullGroup]

/-- `⁅[[T]], [[T]]⁆`, as homeomorphisms, is isomorphic to `⁅fullGroup T, fullGroup T⁆`. -/
noncomputable def derivedTopologicalFullGroupMulEquiv [CompactSpace X] [T2Space X]
    (T : X ≃ₜ X) :
    ↥(⁅topologicalFullGroup T, topologicalFullGroup T⁆ : Subgroup (X ≃ₜ X)) ≃*
      ↥⁅fullGroup T, fullGroup T⁆ :=
  ((⁅topologicalFullGroup T, topologicalFullGroup T⁆ : Subgroup (X ≃ₜ X)).equivMapOfInjective
    homeoToPerm homeoToPerm_injective).trans
    (MulEquiv.subgroupCongr (map_derivedTopologicalFullGroup T))

/-- **Matui, Theorem 4.9, for `[[T]]'` as homeomorphisms**: for a minimal homeomorphism `T` of an
infinite compact Hausdorff totally separated space, `⁅[[T]], [[T]]⁆` is simple. -/
theorem isSimpleGroup_derivedTopologicalFullGroup [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X) (hmin : IsMinimalHomeo T) :
    IsSimpleGroup ↥(⁅topologicalFullGroup T, topologicalFullGroup T⁆ : Subgroup (X ≃ₜ X)) := by
  haveI : IsSimpleGroup ↥⁅fullGroup T, fullGroup T⁆ := isSimpleGroup_commutator_fullGroup T hmin
  exact (derivedTopologicalFullGroupMulEquiv T).isSimpleGroup

end Transport

/-- **Printed** (tex l.307–309, Matui, Theorem 4.9, for Cantor minimal systems): the derived
topological full group `⁅[[T]], [[T]]⁆ ≤ Homeo(X)` of a minimal homeomorphism `T` of a Cantor
space `X` (compact, metrizable, totally disconnected, perfect, nonempty) is simple. -/
def PrintedMatuiCantorMinimal : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X),
    IsMinimalHomeo T →
      IsSimpleGroup ↥(⁅topologicalFullGroup T, topologicalFullGroup T⁆ : Subgroup (X ≃ₜ X))

theorem printedMatuiCantorMinimal : PrintedMatuiCantorMinimal.{u} := by
  intro X _ _ _ _ _ _ T hmin
  haveI : TotallySeparatedSpace X :=
    totallySeparatedSpace_of_t0_of_basis_clopen isTopologicalBasis_isClopen
  haveI : Infinite X :=
    GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.infinite_of_perfectSpace
  exact isSimpleGroup_derivedTopologicalFullGroup T hmin

end GroupApproximation.Full.SKTFGMatui

#audit_axioms GroupApproximation.Full.SKTFGMatui.map_topologicalFullGroup
#audit_axioms GroupApproximation.Full.SKTFGMatui.map_derivedTopologicalFullGroup
#audit_axioms GroupApproximation.Full.SKTFGMatui.isSimpleGroup_derivedTopologicalFullGroup
#audit_closed_axioms GroupApproximation.Full.SKTFGMatui.printedMatuiCantorMinimal
