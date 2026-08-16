import GroupApproximation.Sofic.LiteralVerticalBridge
import GroupApproximation.Sofic.LiteralBlockCliffordBridge
import GroupApproximation.Sofic.LiteralAffineCosetTransitivity
import GroupApproximation.Sofic.LiteralBlockGeometry
import GroupApproximation.Sofic.LiteralSoficEndpoint

/-!
# The literal finitely presented non-MF group is sofic

This file closes the soficity chain for the literal eight-generator,
forty-one-relator group `E` of `def:E`.  Every input is proved in this
repository; the conclusion `markedGroup_isSofic : IsSofic MarkedGroup` carries
no hypothesis, no `sorry`, and no literature axiom.

## What was missing, and what supplies it

`Sofic/BlockCliffordTowerSofic.lean` already proves the general theorem the
chain needs:

    isSofic_blockClifford_tower :
      residually finite base Γ, injective α, an action of `Vertical α hα` on
      `BlockClifford I B` by site permutations fixing the sign, with finite
      level orbits on sites  ⟹  IsSofic (BlockClifford I B ⋊ Vertical α hα).

`Sofic/LiteralBlockCliffordBridge.lean` already presents `E` in exactly that
shape — `markedGroupEquivTower` — modulo two facts about the orbital graph,
and its closing remark records the obstruction to combining them: its
`Vertical` is `PresentedGroup verticalRelators`, while the tower theorem's is
`MarkedCompression.Vertical`, and "the two are unrelated types".

`Sofic/LiteralVerticalBridge.lean` removes that: the two carriers are both
`E/⟨⟨c⟩⟩` and are identified there, together with their site sets and their
orbital graphs.  With that identification the two open graph facts become the
geometry lane's theorems:

* `IsIrreflexive` is `LiteralBlockGeometry.markedSite_ne`, i.e. `v₁ ∉ α(Γ̄)`
  (`ExplicitLinearModel.v1G_not_mem_range`);
* `IsCompleteOnBlocks` is `LiteralBlockGeometry.adj_of_blockOf_eq` fed with
  `LiteralAffineCosetTransitivity.conjD_cosetTransitive`, the CRW-free
  computation that the three displayed rotations move `ē₁` onto all seven
  nonzero classes of `(ℤ/2)³`.

## Where the residual finiteness comes from

Not from Karrass--Pietrowski--Solitar.  The tower's window subgroups are
residually finite by `BlockCliffordLamp.residuallyFinite_blockClifford` and
`BlockCliffordTowerSofic.residuallyFinite_window`, whose proof is the
two-quotient separation: kill the central sign and land in a free product of
finitely many finite sign groups, or keep the sign and land in the finite
complete Clifford model; the two kernels meet trivially because the only thing
the first loses is central and the second keeps it.  That is
`docs/E_SOFICITY_SELF_CONTAINED_2026-08-16.md` §§7--8, and it needs no
virtual-freeness theorem.

The final `ℤ` step is `SoficIntegerExtension.isSofic_int_semidirectProduct`,
the cyclic-truncation construction of that document's §11, not a citation of
Elek--Szabó.

## The blocks here are the presented ones

`LiteralBlockNormalForm.blockSubgroup = ⟨B, β⟩` is only known to be contained
in the geometric `B₁ = τ⁻¹Bτ`, so the presented blocks a priori *refine* the
geometric ones.  That is the direction the argument needs, and nothing below
asserts the reverse: a presented block is finite because it embeds in a
geometric one, and distinct sites of a presented block are adjacent because
they lie in a common geometric block.  (The two facts together force the two
block sets to coincide, but that is a consequence, not an input.)
-/

namespace GroupApproximation
namespace LiteralSoficAssembly

-- `LiteralBlockCliffordBridge.siteEquiv` (sites over blocks) and
-- `LiteralVerticalBridge.siteEquiv` (the two lanes' site sets) are different
-- maps with the same name; the second is the one used unqualified here.
open LiteralNonMFPresentation LiteralBlockNormalForm
open LiteralBlockCliffordBridge hiding siteEquiv
open LiteralVerticalBridge
open MarkedCompression

noncomputable section

/-- The doubling endomorphism of the affine base, as the soficity chain uses
it. -/
abbrev alpha : ExplicitLinearModel.gammaBar →* ExplicitLinearModel.gammaBar :=
  LiteralNonMFLinearWitness.alpha

/-- Its injectivity. -/
theorem halpha : Function.Injective alpha := ExplicitLinearModel.conjD_injective

/-! ## The two graph hypotheses -/

/-- **The two marked sites are distinct.**  Transported from
`LiteralBlockGeometry.markedSite_ne`, whose input is `v₁ ∉ α(Γ̄)`. -/
theorem siteA_ne_siteB : (siteA : Site) ≠ siteB := by
  intro h
  have hgeom := congrArg siteEquiv h
  rw [siteEquiv_siteA, siteEquiv_siteB] at hgeom
  exact LiteralBlockGeometry.markedSite_ne alpha halpha
    ExplicitLinearModel.v1G_not_mem_range hgeom

/-- **No site is adjacent to itself.** -/
theorem isIrreflexive : IsIrreflexive :=
  isIrreflexive_of_siteA_ne_siteB siteA_ne_siteB

/-- **Each block is a complete graph.**  Two distinct sites of one presented
block lie in one geometric block, and the geometry lane's transitivity makes
distinct sites of a geometric block adjacent. -/
theorem isCompleteOnBlocks : IsCompleteOnBlocks := by
  intro ξ η hblock hne
  rw [adjacent_iff]
  refine LiteralBlockGeometry.adj_of_blockOf_eq alpha halpha
    LiteralAffineCosetTransitivity.conjD_cosetTransitive
    (fun h ↦ hne (siteEquiv.injective h)) ?_
  exact blockOf_eq_of_blockOf_eq hblock

/-! ## The blocks are finite

A presented block embeds in a geometric one, and the geometric blocks are
finite because `α` has finite index — `LiteralBaseDoublingIndex` supplies that
instance, and no exact value of the index is used. -/

instance finite_blockSites (b : Block) : Finite (BlockSites b) := by
  classical
  obtain ⟨ξ₀, hξ₀⟩ := LiteralBlockNormalForm.blockOf_surjective b
  have hfib : ∀ ξ : BlockSites b,
      LiteralBlockGeometry.blockOf alpha halpha (siteEquiv (ξ : Site))
        = LiteralBlockGeometry.blockOf alpha halpha (siteEquiv ξ₀) := by
    intro ξ
    exact blockOf_eq_of_blockOf_eq (by rw [ξ.2, hξ₀])
  have hindex : (alpha.range).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  haveI : Finite ↥(LiteralBlockGeometry.blockFibre alpha halpha
      (LiteralBlockGeometry.blockOf alpha halpha (siteEquiv ξ₀))) :=
    LiteralBlockGeometry.finite_blockFibre alpha halpha hindex _
  refine Finite.of_injective
    (fun ξ : BlockSites b ↦
      (⟨siteEquiv (ξ : Site), hfib ξ⟩ :
        ↥(LiteralBlockGeometry.blockFibre alpha halpha
          (LiteralBlockGeometry.blockOf alpha halpha (siteEquiv ξ₀))))) ?_
  intro ξ η h
  exact Subtype.ext (siteEquiv.injective (congrArg Subtype.val h))

instance fintype_blockSites (b : Block) : Fintype (BlockSites b) :=
  Fintype.ofFinite _

instance decEq_blockSites (b : Block) : DecidableEq (BlockSites b) :=
  Classical.decEq _

instance decEq_block : DecidableEq Block := Classical.decEq _

/-! ## Transporting a semidirect product along the acting group

Mathlib has no `SemidirectProduct.congr`; the right-hand congruence is the
only one needed and it is immediate, because the action of the transported
group is the composite. -/

/-- Reindex the acting group of a semidirect product along an isomorphism. -/
def semidirectCongrRight {N H H' : Type*} [Group N] [Group H] [Group H']
    (e : H' ≃* H) (φ : H →* MulAut N) :
    (N ⋊[φ.comp e.toMonoidHom] H') ≃* (N ⋊[φ] H) where
  toFun p := ⟨p.left, e p.right⟩
  invFun q := ⟨q.left, e.symm q.right⟩
  left_inv p := SemidirectProduct.ext rfl (e.symm_apply_apply p.right)
  right_inv q := SemidirectProduct.ext rfl (e.apply_symm_apply q.right)
  map_mul' p q := SemidirectProduct.ext rfl (map_mul e p.right q.right)

/-! ## The literal tower over the telescope carrier -/

/-- The action of the *telescope* vertical group on the block Clifford group,
obtained from the presented one along the bridge. -/
def towerAction :
    MarkedCompression.Vertical alpha halpha →*
      MulAut (BlockCliffordLamp.BlockClifford Block BlockSites) :=
  (blockAutHom isCompleteOnBlocks isIrreflexive).comp
    verticalEquiv.symm.toMonoidHom

/-- **`E` is a block-Clifford tower over the telescope carrier.** -/
def markedGroupEquivTelescopeTower :
    MarkedGroup ≃*
      (BlockCliffordLamp.BlockClifford Block BlockSites ⋊[towerAction]
        MarkedCompression.Vertical alpha halpha) :=
  (markedGroupEquivTower isCompleteOnBlocks isIrreflexive).trans
    (semidirectCongrRight verticalEquiv.symm
      (blockAutHom isCompleteOnBlocks isIrreflexive)).symm

/-- The site permutations induced by the telescope. -/
def teleSitePerm :
    MappingTelescope.Telescope alpha halpha →*
      Equiv.Perm ((b : Block) × BlockSites b) :=
  sitePermHom.comp (verticalEquiv.symm.toMonoidHom.comp
    (SemidirectProduct.inl :
      MappingTelescope.Telescope alpha halpha →*
        MarkedCompression.Vertical alpha halpha))

theorem teleSitePerm_apply (t : MappingTelescope.Telescope alpha halpha)
    (p : (b : Block) × BlockSites b) :
    teleSitePerm t p =
      LiteralBlockCliffordBridge.siteEquiv.symm
        (verticalEquiv.symm (SemidirectProduct.inl t) •
          LiteralBlockCliffordBridge.siteEquiv p) := rfl

/-- The tower action fixes the sign. -/
theorem towerAction_sign (v : MarkedCompression.Vertical alpha halpha) :
    towerAction v (BlockCliffordLamp.sign Block BlockSites) = BlockCliffordLamp.sign Block BlockSites :=
  blockAutHom_sign isCompleteOnBlocks isIrreflexive _

/-- The tower action permutes the lamps along `teleSitePerm`. -/
theorem towerAction_lamp (t : MappingTelescope.Telescope alpha halpha)
    (p : (b : Block) × BlockSites b) :
    towerAction (SemidirectProduct.inl t) (BlockCliffordLamp.lamp Block BlockSites p)
      = BlockCliffordLamp.lamp Block BlockSites (teleSitePerm t p) :=
  blockAutHom_lamp isCompleteOnBlocks isIrreflexive _ p

/-! ## Finite level orbits on sites

`MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit` is the statement over
the geometric site set; the two site identifications are injections, so it
transports. -/

theorem finite_level_site_orbit (n : ℕ) (p : (b : Block) × BlockSites b) :
    (Set.range fun h : ↥(MappingTelescope.level alpha halpha n).range ↦
      teleSitePerm (h : MappingTelescope.Telescope alpha halpha) p).Finite := by
  classical
  have hgeom :
      (Set.range fun h : ↥(MappingTelescopeFiniteOrbits.verticalLevel
          alpha halpha n) ↦
        (h : MarkedCompression.Vertical alpha halpha) •
          LiteralVerticalBridge.siteEquiv
            (LiteralBlockCliffordBridge.siteEquiv p)).Finite :=
    MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit alpha halpha n _
  refine Set.Finite.subset (hgeom.image
    (fun x ↦ LiteralBlockCliffordBridge.siteEquiv.symm
      (LiteralVerticalBridge.siteEquiv.symm x))) ?_
  rintro _ ⟨h, rfl⟩
  obtain ⟨u, hu⟩ := h.2
  refine ⟨LiteralVerticalBridge.siteEquiv
      (verticalEquiv.symm (SemidirectProduct.inl
          (h : MappingTelescope.Telescope alpha halpha)) •
        LiteralBlockCliffordBridge.siteEquiv p), ?_, ?_⟩
  · refine ⟨⟨SemidirectProduct.inl (h : MappingTelescope.Telescope alpha halpha),
      ⟨u, by rw [MonoidHom.comp_apply, hu]⟩⟩, ?_⟩
    rw [siteEquiv_smul, MulEquiv.apply_symm_apply]
  · rw [teleSitePerm_apply, Equiv.symm_apply_apply]

/-! ## The endpoint -/

/-- **The literal forty-one-relator group `E` is sofic.**

Unconditional: no hypothesis, no literature input.  The lamp layer is the
block-Clifford window tower, the telescope layer is the level-by-level
residual finiteness of those windows, and the stable letter is the cyclic
truncation of `SoficIntegerExtension`. -/
theorem markedGroup_isSofic : IsSofic MarkedGroup := by
  have htower :
      IsSofic (BlockCliffordLamp.BlockClifford Block BlockSites ⋊[towerAction]
        MarkedCompression.Vertical alpha halpha) :=
    BlockCliffordTowerSofic.isSofic_blockClifford_tower Block BlockSites
      ExplicitIntegralLinearModel.gammaBar_residuallyFinite alpha halpha
      towerAction teleSitePerm towerAction_sign towerAction_lamp
      finite_level_site_orbit
  exact (isSofic_mulEquiv_iff markedGroupEquivTelescopeTower).mpr htower

/-- **The literal group is hyperlinear.** -/
theorem markedGroup_isHyperlinear : IsHyperlinear MarkedGroup :=
  isHyperlinear_of_isSofic markedGroup_isSofic

/-- **The printed separation.**  An explicit finitely presented group that is
sofic and is not MF. -/
theorem markedGroup_finitelyPresented_sofic_not_isCDEOperatorMF :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  LiteralSoficEndpoint.markedGroup_finitelyPresented_sofic_not_isCDEOperatorMF
    markedGroup_isSofic

/-- **The full endpoint package**, with soficity now discharged: finitely
presented, sofic, hyperlinear, not LEF, not residually finite, and not MF in
every convention the development formalizes. -/
theorem markedGroup_soficNonMF_package :
    Group.IsFinitelyPresented MarkedGroup ∧
      IsSofic MarkedGroup ∧
      IsHyperlinear MarkedGroup ∧
      ¬ IsLEF MarkedGroup ∧
      ¬ Group.ResiduallyFinite MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup ∧
      ¬ IsOperatorMF MarkedGroup ∧
      ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar MarkedGroup) :=
  LiteralSoficEndpoint.markedGroup_soficNonMF_package markedGroup_isSofic

/-- **The sofic radical is trivial while the MF radical is not.**  `E` is
sofic, so it embeds in a sofic group by the identity; the marked involution
`w` is nontrivial and dies in every corona representation. -/
theorem markedGroup_sofic_not_isLEF :
    IsSofic MarkedGroup ∧ ¬ IsLEF MarkedGroup ∧
      ¬ Group.ResiduallyFinite MarkedGroup :=
  LiteralSoficEndpoint.markedGroup_sofic_not_isLEF markedGroup_isSofic

end

end LiteralSoficAssembly
end GroupApproximation
