import GroupApproximation.Sofic.LiteralVerticalBridge
import GroupApproximation.Sofic.LiteralAffineCosetTransitivity
import GroupApproximation.Sofic.BlockCliffordTowerSofic

/-!
# The literal finitely presented non-MF group is sofic

`markedGroup_isSofic : IsSofic MarkedGroup`, with no hypothesis, no incomplete
proof step and no literature input.

## What was missing

`Sofic/BlockCliffordTowerSofic.lean` already proves the general theorem:

    isSofic_blockClifford_tower :
      residually finite base Γ, injective α, an action of `Vertical α hα` on
      `BlockClifford I B` by site permutations fixing the sign, with finite
      level orbits on sites  ⟹  IsSofic (BlockClifford I B ⋊ Vertical α hα).

and `Sofic/LiteralBlockNormalForm.lean` already computes `E ≅ C(𝒢) ⋊ Vertical`.
The two never met because they speak about different vertical groups —
`PresentedGroup verticalRelators` and `MarkedCompression.Vertical` — which
`Sofic/LiteralBlockCliffordBridge.lean` records as "unrelated types".

`Sofic/LiteralVerticalBridge.lean` shows they are the same group.  This file
spends that identification:

* the two graph facts the tower needs become geometry-lane theorems —
  irreflexivity is `v₁ ∉ conjD(Γ̄)` and completeness on blocks is
  `adj_of_blockOf_eq` fed with the CRW-free `conjD_cosetTransitive`;
* the blocks are finite because the *presented* blocks refine the geometric
  ones, which are finite by the doubling index.  No exact value of the index
  is used;
* the lamp factor `C(𝒢)` and the block-Clifford group of the fibred site set
  are identified by their two universal properties, `lampLift` one way and
  `PresentedGroup.toGroup` the other.

Residual finiteness of the windows is `BlockCliffordLamp`'s two-quotient
separation, so **Karrass--Pietrowski--Solitar is not used**; the final `ℤ`
step is `SoficIntegerExtension.isSofic_int_semidirectProduct`.  Both are
`notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md` §§7--8 and §11.
-/

namespace GroupApproximation
namespace LiteralSoficAssembly

open LiteralNonMFPresentation LiteralBlockNormalForm LiteralVerticalBridge
open BlockCliffordLamp
open scoped commutatorElement

noncomputable section

/-- The doubling endomorphism of the affine base. -/
abbrev alpha : ExplicitLinearModel.gammaBar →* ExplicitLinearModel.gammaBar :=
  LiteralNonMFLinearWitness.alpha

theorem halpha : Function.Injective alpha := ExplicitLinearModel.conjD_injective

/-! ## The two graph facts -/

/-- **The two marked sites are distinct**, transported from
`LiteralBlockGeometry.markedSite_ne`, whose input is `v₁ ∉ α(Γ̄)`. -/
theorem siteA_ne_siteB : (siteA : Site) ≠ siteB := by
  intro h
  have hgeom := congrArg siteEquiv h
  rw [siteEquiv_siteA, siteEquiv_siteB] at hgeom
  exact LiteralBlockGeometry.markedSite_ne alpha halpha
    ExplicitLinearModel.v1G_not_mem_range hgeom

/-- **No site is adjacent to itself.** -/
theorem not_adjacent_self (ξ : Site) : ¬ Adjacent ξ ξ := by
  have key : ∀ g : Vertical, g • siteA = ξ → g • siteB = ξ → False := by
    intro g ha hb
    refine siteA_ne_siteB ?_
    have := ha.trans hb.symm
    have h2 := congrArg (fun z ↦ g⁻¹ • z) this
    simpa only [inv_smul_smul] using h2
  rintro (⟨g, ha, hb⟩ | ⟨g, ha, hb⟩)
  · exact key g ha hb
  · exact key g ha hb

/-- **Each block is a complete graph.**  Two distinct sites of one presented
block lie in one geometric block, and the geometry lane's transitivity makes
distinct sites of a geometric block adjacent. -/
theorem adjacent_of_blockOf_eq {ξ η : Site} (hblock : blockOf ξ = blockOf η)
    (hne : ξ ≠ η) : Adjacent ξ η := by
  rw [adjacent_iff]
  exact LiteralBlockGeometry.adj_of_blockOf_eq alpha halpha
    LiteralAffineCosetTransitivity.conjD_cosetTransitive
    (fun h ↦ hne (siteEquiv.injective h)) (blockOf_eq_of_blockOf_eq hblock)

/-! ## The site set fibred over the blocks -/

/-- The sites of one block. -/
abbrev BlockSites (b : Block) : Type := {ξ : Site // blockOf ξ = b}

/-- The site carried by a fibred pair. -/
def siteOf (p : (b : Block) × BlockSites b) : Site := (p.2 : Site)

@[simp] theorem blockOf_siteOf (p : (b : Block) × BlockSites b) :
    blockOf (siteOf p) = p.1 := p.2.2

/-- The fibred pair carried by a site. -/
def pairOf (ξ : Site) : (b : Block) × BlockSites b := ⟨blockOf ξ, ⟨ξ, rfl⟩⟩

@[simp] theorem siteOf_pairOf (ξ : Site) : siteOf (pairOf ξ) = ξ := rfl

@[simp] theorem pairOf_siteOf (p : (b : Block) × BlockSites b) :
    pairOf (siteOf p) = p := by
  obtain ⟨b, ξ, hξ⟩ := p
  subst hξ
  rfl

theorem pairOf_injective : Function.Injective pairOf :=
  Function.LeftInverse.injective siteOf_pairOf

/-! ## The blocks are finite

A presented block embeds in a geometric one, and geometric blocks are finite
because `α` has finite index — no exact value of the index is used. -/

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

/-- The block-Clifford group of the fibred literal site set. -/
abbrev LiteralBlockClifford : Type := BlockClifford Block BlockSites

/-! ## The lamp factor is the block-Clifford group

Both are presented groups, so the identification is their two universal
properties; no normal form and no relator-set image is involved. -/

/-- `C(𝒢) → BlockClifford`, by the universal property of the Clifford graph
group.  The braiding hypothesis is exactly that adjacent sites are distinct
sites of a common block. -/
def toBlock : LiteralBlockNormalForm.LampFactor →* LiteralBlockClifford :=
  lampLift (sign Block BlockSites) (fun ξ ↦ lamp Block BlockSites (pairOf ξ))
    (sign_sq Block BlockSites)
    (fun ξ ↦ lamp_sq Block BlockSites _)
    (fun ξ ↦ sign_commute_lamp Block BlockSites _)
    (by
      intro ξ η hadj
      refine commutator_lamp_lamp' Block BlockSites ?_ ?_
      · show blockOf ξ = blockOf η
        exact blockOf_eq_of_adjacent hadj
      · intro hpq
        have hξη : ξ = η := by
          have := congrArg siteOf hpq
          simpa only [siteOf_pairOf] using this
        exact not_adjacent_self η (hξη ▸ hadj))

@[simp] theorem toBlock_sign : toBlock lampSign = sign Block BlockSites :=
  lampLift_sign _ _ _ _ _ _

@[simp] theorem toBlock_at (ξ : Site) :
    toBlock (lampAt ξ) = lamp Block BlockSites (pairOf ξ) :=
  lampLift_at _ _ _ _ _ _ ξ

/-- `BlockClifford → C(𝒢)`, by the universal property of the block-Clifford
presentation.  The braiding hypothesis is exactly completeness on blocks. -/
def fromBlock : LiteralBlockClifford →* LiteralBlockNormalForm.LampFactor := by
  refine PresentedGroup.toGroup
    (f := Sum.elim (fun _ ↦ lampSign) fun p ↦ lampAt (siteOf p)) ?_
  intro w hw
  change IsRelator Block BlockSites w at hw
  cases hw with
  | sign_sq => rw [map_pow, FreeGroup.lift_apply_of]; exact lampSign_sq
  | lamp_sq p => rw [map_pow, FreeGroup.lift_apply_of]; exact lampAt_sq _
  | sign_comm p =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of]
      exact (lampSign_commute_lampAt _).commutator_eq
  | @braiding i b b' hne =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅lampAt (b : Site), lampAt (b' : Site)⁆ * lampSign⁻¹ = 1
      rw [commutator_lampAt (adjacent_of_blockOf_eq
        (by rw [b.2, b'.2])
        (fun h ↦ hne (Subtype.ext h)))]
      exact mul_inv_cancel _

@[simp] theorem fromBlock_sign : fromBlock (sign Block BlockSites) = lampSign :=
  PresentedGroup.toGroup.of _

@[simp] theorem fromBlock_lamp (p : (b : Block) × BlockSites b) :
    fromBlock (lamp Block BlockSites p) = lampAt (siteOf p) :=
  PresentedGroup.toGroup.of _

theorem fromBlock_comp_toBlock :
    fromBlock.comp toBlock = MonoidHom.id LiteralBlockNormalForm.LampFactor := by
  refine PresentedGroup.ext ?_
  intro j
  match j with
  | Sum.inl () =>
      show fromBlock (toBlock lampSign) = lampSign
      rw [toBlock_sign, fromBlock_sign]
  | Sum.inr ξ =>
      show fromBlock (toBlock (lampAt ξ)) = lampAt ξ
      rw [toBlock_at, fromBlock_lamp, siteOf_pairOf]

theorem toBlock_comp_fromBlock :
    toBlock.comp fromBlock = MonoidHom.id LiteralBlockClifford := by
  refine PresentedGroup.ext ?_
  intro j
  match j with
  | Sum.inl () =>
      show toBlock (fromBlock (sign Block BlockSites)) = sign Block BlockSites
      rw [fromBlock_sign, toBlock_sign]
  | Sum.inr p =>
      show toBlock (fromBlock (lamp Block BlockSites p))
        = lamp Block BlockSites p
      rw [fromBlock_lamp, toBlock_at, pairOf_siteOf]

/-- **The lamp factor of `E` is the block-Clifford group of its site set.** -/
def lampEquiv : LiteralBlockNormalForm.LampFactor ≃* LiteralBlockClifford :=
  MonoidHom.toMulEquiv toBlock fromBlock fromBlock_comp_toBlock
    toBlock_comp_fromBlock

@[simp] theorem lampEquiv_apply (n : LiteralBlockNormalForm.LampFactor) :
    lampEquiv n = toBlock n := rfl

@[simp] theorem lampEquiv_symm_apply (n : LiteralBlockClifford) :
    lampEquiv.symm n = fromBlock n := rfl

/-! ## The vertical action, transported -/

/-- The vertical action on the block-Clifford group. -/
def blockAutHom : Vertical →* MulAut LiteralBlockClifford where
  toFun v := lampEquiv.symm.trans ((lampAutHom v).trans lampEquiv)
  map_one' := by
    refine MulEquiv.ext fun n ↦ ?_
    show lampEquiv (lampAutHom 1 (lampEquiv.symm n)) = n
    rw [map_one]
    exact lampEquiv.apply_symm_apply n
  map_mul' v w := by
    refine MulEquiv.ext fun n ↦ ?_
    show lampEquiv (lampAutHom (v * w) (lampEquiv.symm n))
      = lampEquiv (lampAutHom v (lampEquiv.symm
          (lampEquiv (lampAutHom w (lampEquiv.symm n)))))
    rw [lampEquiv.symm_apply_apply, map_mul]
    rfl

@[simp] theorem blockAutHom_apply (v : Vertical) (n : LiteralBlockClifford) :
    blockAutHom v n = lampEquiv (lampAutHom v (lampEquiv.symm n)) := rfl

theorem blockAutHom_sign (v : Vertical) :
    blockAutHom v (sign Block BlockSites) = sign Block BlockSites := by
  rw [blockAutHom_apply, lampEquiv_symm_apply, fromBlock_sign, lampAutHom_sign,
    lampEquiv_apply, toBlock_sign]

/-- The permutation of the fibred site set induced by a vertical element. -/
def sitePerm (v : Vertical) : Equiv.Perm ((b : Block) × BlockSites b) where
  toFun p := pairOf (v • siteOf p)
  invFun p := pairOf (v⁻¹ • siteOf p)
  left_inv p := by simp only [siteOf_pairOf, inv_smul_smul, pairOf_siteOf]
  right_inv p := by simp only [siteOf_pairOf, smul_inv_smul, pairOf_siteOf]

@[simp] theorem sitePerm_apply (v : Vertical)
    (p : (b : Block) × BlockSites b) : sitePerm v p = pairOf (v • siteOf p) :=
  rfl

/-- The site permutations, as a homomorphism. -/
def sitePermHom : Vertical →* Equiv.Perm ((b : Block) × BlockSites b) where
  toFun := sitePerm
  map_one' := by
    refine Equiv.ext fun p ↦ ?_
    rw [sitePerm_apply, one_smul, pairOf_siteOf]
    rfl
  map_mul' v w := by
    refine Equiv.ext fun p ↦ ?_
    show pairOf ((v * w) • siteOf p) = sitePerm v (sitePerm w p)
    rw [sitePerm_apply, sitePerm_apply, siteOf_pairOf, mul_smul]

theorem blockAutHom_lamp (v : Vertical) (p : (b : Block) × BlockSites b) :
    blockAutHom v (lamp Block BlockSites p)
      = lamp Block BlockSites (sitePerm v p) := by
  rw [blockAutHom_apply, lampEquiv_symm_apply, fromBlock_lamp, lampAutHom_at,
    lampEquiv_apply, toBlock_at, sitePerm_apply]

/-! ## The tower -/

/-- Reindex a semidirect product along isomorphisms of both factors. -/
def semidirectCongr {N N' H H' : Type*} [Group N] [Group N'] [Group H]
    [Group H'] (eN : N ≃* N') (eH : H' ≃* H) (φ : H →* MulAut N)
    (φ' : H' →* MulAut N')
    (hcompat : ∀ (h : H') (n : N), eN (φ (eH h) n) = φ' h (eN n)) :
    (N ⋊[φ] H) ≃* (N' ⋊[φ'] H') where
  toFun p := ⟨eN p.left, eH.symm p.right⟩
  invFun q := ⟨eN.symm q.left, eH q.right⟩
  left_inv p :=
    SemidirectProduct.ext (eN.symm_apply_apply p.left)
      (eH.apply_symm_apply p.right)
  right_inv q :=
    SemidirectProduct.ext (eN.apply_symm_apply q.left)
      (eH.symm_apply_apply q.right)
  map_mul' p q := by
    refine SemidirectProduct.ext ?_ (map_mul eH.symm p.right q.right)
    show eN (p.left * φ p.right q.left)
      = eN p.left * φ' (eH.symm p.right) (eN q.left)
    rw [map_mul]
    congr 1
    have := hcompat (eH.symm p.right) q.left
    rwa [eH.apply_symm_apply] at this

/-- The tower action over the *telescope* vertical group. -/
def towerAction :
    MarkedCompression.Vertical alpha halpha →* MulAut LiteralBlockClifford :=
  blockAutHom.comp verticalEquiv.symm.toMonoidHom

@[simp] theorem towerAction_apply (v : MarkedCompression.Vertical alpha halpha)
    (n : LiteralBlockClifford) :
    towerAction v n = blockAutHom (verticalEquiv.symm v) n := rfl

/-- **`E` is a block-Clifford tower over the telescope carrier.** -/
def markedGroupEquivTelescopeTower :
    MarkedGroup ≃*
      (LiteralBlockClifford ⋊[towerAction]
        MarkedCompression.Vertical alpha halpha) :=
  markedGroupEquivModel.trans
    (semidirectCongr lampEquiv verticalEquiv.symm lampAutHom towerAction
      (by
        intro h n
        rw [towerAction_apply, blockAutHom_apply, lampEquiv.symm_apply_apply]))

/-- The site permutations induced by the telescope. -/
def teleSitePerm :
    MappingTelescope.Telescope alpha halpha →*
      Equiv.Perm ((b : Block) × BlockSites b) :=
  sitePermHom.comp (verticalEquiv.symm.toMonoidHom.comp
    (SemidirectProduct.inl :
      MappingTelescope.Telescope alpha halpha →*
        MarkedCompression.Vertical alpha halpha))

theorem towerAction_sign (v : MarkedCompression.Vertical alpha halpha) :
    towerAction v (sign Block BlockSites) = sign Block BlockSites :=
  blockAutHom_sign _

theorem towerAction_lamp (t : MappingTelescope.Telescope alpha halpha)
    (p : (b : Block) × BlockSites b) :
    towerAction (SemidirectProduct.inl t) (lamp Block BlockSites p)
      = lamp Block BlockSites (teleSitePerm t p) :=
  blockAutHom_lamp _ p

/-! ## Finite level orbits on sites -/

theorem finite_level_site_orbit (n : ℕ) (p : (b : Block) × BlockSites b) :
    (Set.range fun h : ↥(MappingTelescope.level alpha halpha n).range ↦
      teleSitePerm (h : MappingTelescope.Telescope alpha halpha) p).Finite := by
  classical
  have hgeom :
      (Set.range fun h : ↥(MappingTelescopeFiniteOrbits.verticalLevel
          alpha halpha n) ↦
        (h : MarkedCompression.Vertical alpha halpha) •
          siteEquiv (siteOf p)).Finite :=
    MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit alpha halpha n _
  refine Set.Finite.subset (hgeom.image
    (fun x ↦ pairOf (siteEquiv.symm x))) ?_
  rintro _ ⟨h, rfl⟩
  obtain ⟨u, hu⟩ := h.2
  refine ⟨siteEquiv (verticalEquiv.symm (SemidirectProduct.inl
      (h : MappingTelescope.Telescope alpha halpha)) • siteOf p), ?_, ?_⟩
  · refine ⟨⟨SemidirectProduct.inl (h : MappingTelescope.Telescope alpha halpha),
      ⟨u, by rw [MonoidHom.comp_apply, hu]⟩⟩, ?_⟩
    rw [siteEquiv_smul, MulEquiv.apply_symm_apply]
  · exact congrArg pairOf (siteEquiv.symm_apply_apply _)

/-! ## The endpoint -/

/-- **The literal forty-one-relator group `E` is sofic.**

Unconditional: no hypothesis, no literature input.  The lamp layer is the
block-Clifford window tower, the telescope layer is the level-by-level
residual finiteness of those windows, and the stable letter is the cyclic
truncation of `SoficIntegerExtension`. -/
theorem markedGroup_isSofic : IsSofic MarkedGroup := by
  have htower :
      IsSofic (LiteralBlockClifford ⋊[towerAction]
        MarkedCompression.Vertical alpha halpha) :=
    BlockCliffordTowerSofic.isSofic_blockClifford_tower Block BlockSites
      ExplicitIntegralLinearModel.gammaBar_residuallyFinite alpha halpha
      towerAction teleSitePerm towerAction_sign towerAction_lamp
      finite_level_site_orbit
  exact (isSofic_mulEquiv_iff markedGroupEquivTelescopeTower).mpr htower

end

end LiteralSoficAssembly
end GroupApproximation
