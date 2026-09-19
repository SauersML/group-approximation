import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Statements
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiSimplicity
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerPerm
import GroupApproximation.Meta.AxiomGuard

/-!
# Matui's theorem for `[[T]]'` as homeomorphisms (census row `3eaee0a2dc7e`)

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

`Full.SKTFG.MatuiDerivedFullGroupSimpleStatement` states Matui's Theorem 4.9 for the derived
topological full group `[[T]]' = ⁅[[T]], [[T]]⁆` of a Cantor minimal system, with `[[T]]` the
subgroup `topologicalFullGroup T` of the homeomorphism group (`FlipConverse.FullGroup`).  The
StepanovMatui lane proved Matui's theorem for `[[T]]` as the subgroup `fullGroup T` of the
permutation group (`Full.StepanovMatui.Matui.isSimpleGroup_commutator_fullGroup`, with Lemma 3.4
as `alternatingFullGroup_le_of_ne_bot`).  This file moves that theorem across the two encodings.

* `map_topologicalFullGroup`: on a compact Hausdorff space, forgetting continuity
  (`homeoToPerm`) maps `topologicalFullGroup T` onto `fullGroup T`.  An element of `fullGroup T`
  is continuous, and by compactness so is its inverse, so it is a homeomorphism.
* `map_derivedFullGroup`, `derivedFullGroupMulEquiv`: hence `[[T]]' ≃* ⁅fullGroup T, fullGroup T⁆`,
  since `homeoToPerm` is injective and maps commutator subgroups to commutator subgroups.
* `isSimpleGroup_derivedFullGroup`: `[[T]]'` is simple for a minimal homeomorphism of an infinite
  compact Hausdorff totally separated space.
* `matuiDerivedFullGroupSimple`: the closed statement `MatuiDerivedFullGroupSimpleStatement`.  A
  Cantor minimal system is compact, metrizable (so Hausdorff), totally disconnected (so totally
  separated, having a clopen basis) and perfect and nonempty (so infinite).
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

/-- Forgetting continuity maps `[[T]]'` onto `⁅fullGroup T, fullGroup T⁆`. -/
theorem map_derivedFullGroup [CompactSpace X] [T2Space X] (T : X ≃ₜ X) :
    (SKTFG.derivedFullGroup T).map homeoToPerm = ⁅fullGroup T, fullGroup T⁆ := by
  unfold SKTFG.derivedFullGroup
  rw [Subgroup.map_commutator, map_topologicalFullGroup]

/-- `[[T]]'`, as homeomorphisms, is isomorphic to `⁅fullGroup T, fullGroup T⁆`. -/
noncomputable def derivedFullGroupMulEquiv [CompactSpace X] [T2Space X] (T : X ≃ₜ X) :
    SKTFG.derivedFullGroup T ≃* ⁅fullGroup T, fullGroup T⁆ :=
  ((SKTFG.derivedFullGroup T).equivMapOfInjective homeoToPerm homeoToPerm_injective).trans
    (MulEquiv.subgroupCongr (map_derivedFullGroup T))

/-- **Matui, Theorem 4.9, for `[[T]]'` as homeomorphisms**: for a minimal homeomorphism `T` of an
infinite compact Hausdorff totally separated space, `[[T]]'` is simple. -/
theorem isSimpleGroup_derivedFullGroup [CompactSpace X] [T2Space X] [TotallySeparatedSpace X]
    [Infinite X] (T : X ≃ₜ X) (hmin : IsMinimalHomeo T) :
    IsSimpleGroup (SKTFG.derivedFullGroup T) := by
  haveI : IsSimpleGroup ↥⁅fullGroup T, fullGroup T⁆ := isSimpleGroup_commutator_fullGroup T hmin
  exact (derivedFullGroupMulEquiv T).isSimpleGroup

end Transport

/-- **Matui, Theorem 4.9** (census row `3eaee0a2dc7e`, tex l.307–309): for every Cantor minimal
system `(X, T)`, the derived topological full group `[[T]]'` is simple. -/
theorem matuiDerivedFullGroupSimple : SKTFG.MatuiDerivedFullGroupSimpleStatement.{u} := by
  intro X _ T hT
  obtain ⟨hc, hm, htd, hp, hne, hmin⟩ := hT
  haveI := hc
  haveI := hm
  haveI := htd
  haveI := hp
  haveI := hne
  haveI : TotallySeparatedSpace X :=
    totallySeparatedSpace_of_t0_of_basis_clopen isTopologicalBasis_isClopen
  haveI : Infinite X :=
    GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.infinite_of_perfectSpace
  exact isSimpleGroup_derivedFullGroup T hmin

end GroupApproximation.Full.SKTFGMatui

#audit_axioms GroupApproximation.Full.SKTFGMatui.map_topologicalFullGroup
#audit_axioms GroupApproximation.Full.SKTFGMatui.map_derivedFullGroup
#audit_axioms GroupApproximation.Full.SKTFGMatui.isSimpleGroup_derivedFullGroup
#audit_closed_axioms GroupApproximation.Full.SKTFGMatui.matuiDerivedFullGroupSimple
