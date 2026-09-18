import GroupApproximation.Sofic.CliffordLampGraphFreeSubgroup
import GroupApproximation.Sofic.LiteralVerticalBridge
import GroupApproximation.Sofic.LiteralLampKernelAmalgam
import GroupApproximation.Sofic.BlockCliffordLamp
import GroupApproximation.Meta.AxiomGuard

/-!
# The block comparison after the normal form for `E`

Manuscript `non_mf_group_notes.tex`, prose after `prop:blocknormalform`
(ledger row BN.06):

> The group `Cl(X)` is locally finite; `C(𝒢)` is not, since two lamps at sites
> of different blocks generate an infinite dihedral group and three blocks give
> a nonabelian free subgroup. [...] The auxiliary quotient `W/⟨ζ⟩` is an
> ordinary permutational lamp group, but `C(𝒢)/⟨ζ⟩` is the free product of the
> elementary abelian `2`-groups attached to the blocks of `𝒢`.

The rooted files `CliffordLampGraphLocalFiniteness` and
`CliffordLampGraphFreeSubgroup` prove the two structural sentences *under the
hypothesis* that sites in distinct presented blocks are given.  This file
discharges that hypothesis unconditionally:

* the geometric block space `LiteralBlockGeometry.Block` of the literal pair is
  infinite and `LiteralBlockGeometry.blockOf` is surjective;
* `LiteralVerticalBridge.siteEquiv` identifies the presented sites with the
  geometric cosets, and `LiteralVerticalBridge.blockOf_eq_of_blockOf_eq` says
  presented blocks refine geometric blocks;
* so three pairwise distinct geometric blocks give three presented sites in
  pairwise distinct presented blocks.

The two quotient clauses are packaged from the rooted declarations
`LiteralLampKernelAmalgam.signQuotientEquiv` (the lamp factor of the auxiliary
group modulo its sign is elementary abelian) and `BlockCliffordLamp.toFreeBar`
with its left inverse `BlockCliffordLamp.fromFree` (the block-Clifford model
modulo its sign embeds in the free product of the block sign groups).  The
latter is stated at the presented finite-window block-Clifford model, not at
the literal graph group; that substitution is inherited from ledger row BN.06.
-/

namespace GroupApproximation.Full.NN12

/-- **Presented blocks are distinguished by geometric blocks.**  If the
geometric blocks of the corresponding cosets differ, so do the presented
blocks. -/
theorem blockOf_ne_of_geometric_ne {ξ η : LiteralBlockNormalForm.Site}
    (h : LiteralBlockGeometry.blockOf LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective (LiteralVerticalBridge.siteEquiv ξ)
        ≠ LiteralBlockGeometry.blockOf LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective (LiteralVerticalBridge.siteEquiv η)) :
    LiteralBlockNormalForm.blockOf ξ ≠ LiteralBlockNormalForm.blockOf η :=
  fun hb => h (LiteralVerticalBridge.blockOf_eq_of_blockOf_eq hb)

/-- **Three sites in pairwise distinct blocks exist** (`prop:blocknormalform`,
the prose "three blocks").  Unconditional: the geometric block space is
infinite. -/
theorem exists_three_sites_distinct_blocks :
    ∃ ξ η θ : LiteralBlockNormalForm.Site,
      LiteralBlockNormalForm.blockOf ξ ≠ LiteralBlockNormalForm.blockOf η ∧
      LiteralBlockNormalForm.blockOf ξ ≠ LiteralBlockNormalForm.blockOf θ ∧
      LiteralBlockNormalForm.blockOf η ≠ LiteralBlockNormalForm.blockOf θ := by
  let f := Infinite.natEmbedding
    (LiteralBlockGeometry.Block LiteralNonMFLinearWitness.alpha
      ExplicitLinearModel.conjD_injective)
  obtain ⟨c0, h0⟩ := LiteralBlockGeometry.blockOf_surjective
    LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective (f 0)
  obtain ⟨c1, h1⟩ := LiteralBlockGeometry.blockOf_surjective
    LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective (f 1)
  obtain ⟨c2, h2⟩ := LiteralBlockGeometry.blockOf_surjective
    LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective (f 2)
  refine ⟨LiteralVerticalBridge.siteEquiv.symm c0,
    LiteralVerticalBridge.siteEquiv.symm c1,
    LiteralVerticalBridge.siteEquiv.symm c2, ?_, ?_, ?_⟩
  · apply blockOf_ne_of_geometric_ne
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, h0, h1]
    exact f.injective.ne (by decide)
  · apply blockOf_ne_of_geometric_ne
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, h0, h2]
    exact f.injective.ne (by decide)
  · apply blockOf_ne_of_geometric_ne
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, h1, h2]
    exact f.injective.ne (by decide)

/-- **Two lamps at sites of different blocks generate an infinite dihedral
group**: their product has infinite order. -/
theorem orderOf_lampAt_mul_lampAt {ξ η : LiteralBlockNormalForm.Site}
    (hb : LiteralBlockNormalForm.blockOf ξ ≠ LiteralBlockNormalForm.blockOf η) :
    orderOf (LiteralBlockNormalForm.lampAt ξ * LiteralBlockNormalForm.lampAt η) = 0 := by
  have hne : ¬ LiteralBlockNormalForm.Adjacent ξ η :=
    fun hadj => hb (LiteralBlockNormalForm.blockOf_eq_of_adjacent hadj)
  have hd : η ≠ ξ := fun h => hb (by rw [h])
  have hdvd := orderOf_map_dvd (CliffordLampGraph.twoLampLift hne)
    (LiteralBlockNormalForm.lampAt ξ * LiteralBlockNormalForm.lampAt η)
  rw [CliffordLampGraph.twoLampLift_mul hne hd, DihedralGroup.orderOf_r_one] at hdvd
  exact zero_dvd_iff.mp hdvd

/-- **`C(𝒢)` is not locally finite** (`prop:blocknormalform`, prose),
unconditionally. -/
theorem lampFactor_not_isLocallyFiniteGroup :
    ¬ IsLocallyFiniteGroup LiteralBlockNormalForm.LampFactor := by
  obtain ⟨_, _, _, h01, _, _⟩ := exists_three_sites_distinct_blocks
  exact CliffordLampGraph.not_isLocallyFiniteGroup_lampFactor_of_two_blocks h01

/-- **Three blocks give a nonabelian free subgroup of `C(𝒢)`**
(`prop:blocknormalform`, prose), unconditionally, together with the explicit
non-commuting pair of lamp products. -/
theorem lampFactor_exists_nonabelian_free_subgroup :
    ∃ ξ η θ : LiteralBlockNormalForm.Site,
      (∃ H : Subgroup LiteralBlockNormalForm.LampFactor,
          Nonempty (FreeGroup (Fin 2) ≃* H)) ∧
        ¬ Commute (LiteralBlockNormalForm.lampAt ξ * LiteralBlockNormalForm.lampAt η)
          (LiteralBlockNormalForm.lampAt ξ * LiteralBlockNormalForm.lampAt θ) := by
  obtain ⟨ξ, η, θ, h01, h02, h12⟩ := exists_three_sites_distinct_blocks
  exact ⟨ξ, η, θ,
    CliffordLampGraph.exists_nonabelian_free_subgroup_of_three_blocks h01 h02 h12⟩

/-- **The printed block comparison** (ledger BN.06), as one conjunction:

1. the Clifford lamp group on a finite site set modulo its sign is the
   elementary abelian sign group on the sites (the auxiliary quotient is an
   ordinary lamp group);
2. the finite-window block-Clifford model modulo its sign embeds, with an
   explicit left inverse, in the free product of the block sign groups;
3. `C(𝒢)` is not locally finite;
4. `C(𝒢)` contains a free group of rank two. -/
theorem blockComparison_printed :
    (∀ (X : Type) [Fintype X] [DecidableEq X],
        Nonempty (LiteralLampKernelAmalgam.SignQuotient X ≃*
          (X → Multiplicative (ZMod 2)))) ∧
      (∀ (I : Type) [DecidableEq I] [Fintype I] (B : I → Type)
          [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)],
          Function.Injective (BlockCliffordLamp.toFreeBar I B) ∧
            (BlockCliffordLamp.fromFree I B).comp (BlockCliffordLamp.toFreeBar I B)
              = MonoidHom.id (BlockCliffordLamp.BarBlock I B)) ∧
      ¬ IsLocallyFiniteGroup LiteralBlockNormalForm.LampFactor ∧
      ∃ H : Subgroup LiteralBlockNormalForm.LampFactor,
        Nonempty (FreeGroup (Fin 2) ≃* H) := by
  refine ⟨fun X _ _ => ⟨LiteralLampKernelAmalgam.signQuotientEquiv X⟩,
    fun I _ _ B _ _ => ⟨BlockCliffordLamp.toFreeBar_injective I B,
      BlockCliffordLamp.fromFree_comp_toFreeBar I B⟩,
    lampFactor_not_isLocallyFiniteGroup, ?_⟩
  obtain ⟨_, _, _, hfree, _⟩ := lampFactor_exists_nonabelian_free_subgroup
  exact hfree

#audit_axioms blockOf_ne_of_geometric_ne
#audit_axioms exists_three_sites_distinct_blocks
#audit_axioms orderOf_lampAt_mul_lampAt
#audit_axioms lampFactor_not_isLocallyFiniteGroup
#audit_axioms lampFactor_exists_nonabelian_free_subgroup
#audit_axioms blockComparison_printed

end GroupApproximation.Full.NN12
