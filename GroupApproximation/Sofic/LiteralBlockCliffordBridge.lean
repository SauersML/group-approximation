import GroupApproximation.Sofic.LiteralBlockNormalForm
import GroupApproximation.Sofic.BlockCliffordTowerSofic

/-!
# The lamp factor of the literal group is a block Clifford group

**DRAFT — never compiled.**

`Sofic/LiteralBlockNormalForm.lean` computes the literal group as
`Model = LampFactor ⋊[lampAutHom] Vertical`, where `LampFactor` is the Clifford
group of the *orbital graph* `𝒢`: generators a central sign and one involution
per site, with two lamps anticommuting exactly when their sites are
`Adjacent`.  `Sofic/BlockCliffordTowerSofic.lean` proves soficity of
`BlockClifford I B ⋊ Vertical`, where `BlockClifford` is the Clifford group of
a *partitioned* site set: two lamps anticommute exactly when they lie in the
same block, and lamps in different blocks satisfy no relation at all.

These are the same presentation as soon as the orbital graph is a disjoint
union of complete graphs on the blocks.  One half of that is already proved:
`blockOf_eq_of_adjacent` says an edge stays inside a block.  The other half —
that every pair of distinct sites in a common block *is* an edge — is missing
from the repository, and it is the only thing between the two files.  This
module isolates it as `IsCompleteOnBlocks` and shows that it is sufficient:
granted it, the lamp factor is a block Clifford group, the tower theorem
applies, and `IsSofic MarkedGroup` follows.

## What is assumed and what is not

`IsCompleteOnBlocks` is the manuscript's assertion that each block is a
complete graph on eight sites (dossier §4).  It is a statement about the
`Vertical`-orbit of the marked pair, not about approximation, and it needs no
analysis; it is stated here as a hypothesis only because nobody has proved it
in Lean yet.  Everything else below is derived.

Irreflexivity of the edge relation is a second, much smaller hypothesis:
`Adjacent ξ ξ` would force the central sign to be trivial, so the graph
presentation is only the intended one when no site is adjacent to itself.
It is separated out as `IsIrreflexive` rather than folded into the first,
because the two have different proofs — the first is an orbit computation,
the second is `siteA ≠ siteB` transported along the action.
-/

namespace GroupApproximation
namespace LiteralBlockCliffordBridge

open LiteralBlockNormalForm BlockCliffordLamp

noncomputable section

/-! ## Where `IsCompleteOnBlocks` comes from, and what is still missing

`Sofic/LiteralBlockGeometry.lean` proves the abstract form of the completeness
hypothesis: `adj_of_blockOf_eq` derives "distinct sites of one block are
adjacent" from `AlphaCosetTransitive α a₀`, the statement that `α(Γ)` acts
transitively on the nontrivial cosets of `α(Γ)` in `Γ`.  For the affine
doubling that hypothesis is also proved, as `alphaCosetTransitive`.

Neither is usable here yet, for two separate reasons, and both are
identifications rather than mathematics.

*The carrier.*  `alphaCosetTransitive` is proved for
`Monsters/AffineSL3Doubling.alpha` at `AffineSL3Doubling.Gamma`.  This chain
runs over `ExplicitLinearModel.gammaBar` with `alpha = conjD`.  Nothing in the
repository relates the two: there is no `MulEquiv` between the carriers and
none intertwining the endomorphisms, and the only file that mentions both is a
warning comment.  What is needed is `AlphaCosetTransitive conjD a₀` over
`gammaBar` -- the same finite mod-`2` computation, that the reductions of the
three rotation matrices move `ē₁` onto every nonzero class of `(ℤ/2)³`,
carried out for the `4 × 4` rational model instead of the semidirect product.

*The site vocabulary.*  `LiteralBlockGeometry` states its conclusion for its
own `Cosets α hα`, `Adj α hα a₀` and `blockOf α hα`; `LiteralBlockNormalForm`
states `Adjacent` and `blockOf` for its `Site = Vertical ⧸ baseSubgroup`.  The
two are the same construction written twice, and a reader can see that, but
Lean will want the identification spelled out before `adj_of_blockOf_eq`
discharges `IsCompleteOnBlocks` below.

So the honest status is: soficity of the literal group is one finite
arithmetic statement plus two bookkeeping identifications away, and
`IsCompleteOnBlocks` is stated as a hypothesis here rather than derived only
because those identifications have not been written.

Of the two hypotheses below only the first is substantial:
`isIrreflexive_of_siteA_ne_siteB` reduces the second to distinctness of the
two marked sites, which is `moved_cosets_ne` and is already applied at
`alpha`/`conjD_injective` elsewhere in the repository.

## Overlap with the amalgam lane

`Sofic/LiteralLampKernelAmalgam.lean` reaches the same place from the other
side: its §13 discharges `IsBlockCliffordPresentation` for `LampFactor`, and
lands on the same two graph facts under the names `hcomplete` and `hadj_ne`.
Its route additionally proves the block order `512` outright and gives
`isSofic_centralAmalgam` with no hypotheses at all.  The two developments
should be merged once either compiles; the reason to keep both for now is that
they fail differently, and a build pass will say which survives.
-/

/-! ## The two graph hypotheses -/

/-- **Each block is a complete graph.**  Distinct sites in a common block are
adjacent.  With `blockOf_eq_of_adjacent` this says the orbital graph is the
disjoint union of complete graphs indexed by the blocks. -/
def IsCompleteOnBlocks : Prop :=
  ∀ ξ η : Site, blockOf ξ = blockOf η → ξ ≠ η → Adjacent ξ η

/-- **No site is adjacent to itself.** -/
def IsIrreflexive : Prop :=
  ∀ ξ : Site, ¬ Adjacent ξ ξ

/-- Irreflexivity is exactly distinctness of the two marked sites, and needs
no transitivity input: both disjuncts of `Adjacent ξ ξ` produce a `g` with
`g • siteA = g • siteB`, and the action of a group element on its coset space
is injective.

The corresponding fact in the other site vocabulary is `moved_cosets_ne`,
already applied at `alpha`/`conjD_injective` in
`Sofic/LiteralSignFreeQuotient.lean`, so this hypothesis is in the repository
over the right carrier and only the vocabulary identification is missing. -/
theorem isIrreflexive_of_siteA_ne_siteB (h : siteA ≠ siteB) : IsIrreflexive := by
  intro ξ hadj
  have key : ∀ g : Vertical, g • siteA = ξ → g • siteB = ξ → False := by
    intro g ha hb
    exact h (smul_right_injective' (a := g) (ha.trans hb.symm))
  rcases hadj with ⟨g, ha, hb⟩ | ⟨g, ha, hb⟩
  · exact key g ha hb
  · exact key g hb ha
where
  /-- `g • ·` is injective on the coset space. -/
  smul_right_injective' {g : Vertical} {x y : Site} (hxy : g • x = g • y) :
      x = y := by
    have := congrArg (fun z ↦ g⁻¹ • z) hxy
    simpa [inv_smul_smul] using this

/-! ## The block family -/

/-- The sites of a block, as the fibre of `blockOf`. -/
abbrev BlockSites (b : Block) : Type := {ξ : Site // blockOf ξ = b}

/-- The site set is the disjoint union of its blocks. -/
def siteEquiv : ((b : Block) × BlockSites b) ≃ Site :=
  Equiv.sigmaFiberEquiv blockOf

@[simp] theorem siteEquiv_apply (b : Block) (ξ : BlockSites b) :
    siteEquiv ⟨b, ξ⟩ = (ξ : Site) := rfl

@[simp] theorem blockOf_siteEquiv (p : (b : Block) × BlockSites b) :
    blockOf (siteEquiv p) = p.1 := p.2.2

/-- Two sites of the sigma type lie in the same block exactly when their
first components agree. -/
theorem blockOf_eq_iff (p q : (b : Block) × BlockSites b) :
    blockOf (siteEquiv p) = blockOf (siteEquiv q) ↔ p.1 = q.1 := by
  rw [blockOf_siteEquiv, blockOf_siteEquiv]

/-! ## The generator dictionary -/

/-- Generators of the block presentation, transported to generators of the
graph presentation. -/
def genEquiv : Gen Block BlockSites ≃ LampGen :=
  Equiv.sumCongr (Equiv.refl Unit) siteEquiv

@[simp] theorem genEquiv_sign :
    genEquiv (Sum.inl ()) = (Sum.inl () : LampGen) := rfl

@[simp] theorem genEquiv_lamp (p : (b : Block) × BlockSites b) :
    genEquiv (Sum.inr p) = (Sum.inr (siteEquiv p) : LampGen) := rfl

/-- The induced isomorphism of free groups.  `FreeGroup.freeGroupCongr` is the
name `PresentedGroup.equivPresentedGroup` is stated with, so the two compose
without a coercion step. -/
def freeEquiv : FreeGroup (Gen Block BlockSites) ≃* FreeGroup LampGen :=
  FreeGroup.freeGroupCongr genEquiv

/-! ## The relator sets correspond

Both directions need one of the two graph hypotheses, and they need different
ones: sending a block braiding to a graph braiding needs completeness, and
sending a graph braiding to a block braiding needs that adjacency implies both
a common block (proved) and distinctness (irreflexivity). -/

/-- Block relators map to graph relators, given completeness. -/
theorem freeEquiv_maps_relators (hc : IsCompleteOnBlocks) :
    ∀ w ∈ relators Block BlockSites, freeEquiv w ∈ lampRelatorSet := by
  rintro w (- | p | p | ⟨b, ξ, η, hne⟩)
  · exact IsLampRelator.sign_sq
  · exact IsLampRelator.lamp_sq _
  · exact IsLampRelator.sign_comm _
  · refine IsLampRelator.braiding (hc _ _ ?_ ?_)
    · rw [blockOf_siteEquiv, blockOf_siteEquiv]
    · exact fun h ↦ hne (Subtype.ext h)

/-- Graph relators map to block relators, given irreflexivity. -/
theorem freeEquiv_symm_maps_relators (hi : IsIrreflexive) :
    ∀ w ∈ lampRelatorSet, freeEquiv.symm w ∈ relators Block BlockSites := by
  rintro w (- | ξ | ξ | ⟨ξ, η, hadj⟩)
  · exact IsRelator.sign_sq
  · exact IsRelator.lamp_sq _
  · exact IsRelator.sign_comm _
  · have hblock : blockOf ξ = blockOf η := blockOf_eq_of_adjacent hadj
    have hne : ξ ≠ η := by rintro rfl; exact hi _ hadj
    exact IsRelator.braiding (i := blockOf ξ) (by
      intro h
      exact hne (congrArg Subtype.val h))

/-! ## The isomorphism of lamp groups -/

/-- The two relator sets correspond under the generator dictionary. -/
theorem image_relators (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    freeEquiv '' (relators Block BlockSites) = lampRelatorSet := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨w, hw, rfl⟩
    exact freeEquiv_maps_relators hc w hw
  · intro w hw
    refine ⟨freeEquiv.symm w, freeEquiv_symm_maps_relators hi w hw, ?_⟩
    exact freeEquiv.apply_symm_apply w

/-- **The lamp factor is a block Clifford group.**  Given that the orbital
graph is a disjoint union of complete graphs on the blocks, the Clifford group
of the graph and the block Clifford group of the partitioned site set have the
same presentation.

`PresentedGroup.equivPresentedGroup` transports a presentation along an
equivalence of generator types but leaves the relator set as an image; the
second factor rewrites that image to `lampRelatorSet` using
`image_relators`. -/
def lampEquiv (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    BlockClifford Block BlockSites ≃* LampFactor :=
  (PresentedGroup.equivPresentedGroup (relators Block BlockSites) genEquiv).trans
    (QuotientGroup.quotientMulEquivOfEq
      (congrArg Subgroup.normalClosure (image_relators hc hi)))

/-- `lampEquiv` sends the block sign to the graph sign.  Both factors act on a
generator by `PresentedGroup.of ∘ genEquiv` and by `QuotientGroup.mk`
respectively, so this is `equivPresentedGroup_apply_of` followed by
`quotientMulEquivOfEq_mk`; it is not `rfl`, because the second factor is a
transport along a set equality. -/
@[simp] theorem lampEquiv_sign (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    lampEquiv hc hi (sign Block BlockSites) = lampSign := by
  show QuotientGroup.quotientMulEquivOfEq _
      (PresentedGroup.equivPresentedGroup _ genEquiv (PresentedGroup.of _)) = _
  rw [PresentedGroup.equivPresentedGroup_apply_of]
  rfl

@[simp] theorem lampEquiv_lamp (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (p : (b : Block) × BlockSites b) :
    lampEquiv hc hi (lamp Block BlockSites p) = lampAt (siteEquiv p) := by
  show QuotientGroup.quotientMulEquivOfEq _
      (PresentedGroup.equivPresentedGroup _ genEquiv (PresentedGroup.of _)) = _
  rw [PresentedGroup.equivPresentedGroup_apply_of]
  rfl

/-! ## Transporting the vertical action -/

/-- The action of the vertical group on the block Clifford group, conjugated
across `lampEquiv`.  Mathlib has no `MulAut` congruence, so the conjugation is
written out; `map_one'` and `map_mul'` are the two cancellations
`e.symm.trans (1.trans e) = 1` and
`e.symm.trans ((a * b).trans e) = (e.symm.trans (a.trans e)) * (e.symm.trans (b.trans e))`,
both of which hold pointwise by `MulEquiv.apply_symm_apply`. -/
def blockAutHom (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    Vertical →* MulAut (BlockClifford Block BlockSites) where
  toFun v :=
    (lampEquiv hc hi).trans ((lampAutHom v).trans (lampEquiv hc hi).symm)
  map_one' := by
    refine MulEquiv.ext fun n ↦ ?_
    simp [map_one]
  map_mul' v w := by
    refine MulEquiv.ext fun n ↦ ?_
    simp [map_mul, MulAut.mul_apply]

/-- The vertical action fixes the sign. -/
theorem blockAutHom_sign (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (v : Vertical) :
    blockAutHom hc hi v (sign Block BlockSites) = sign Block BlockSites := by
  have := lampAutHom_sign v
  simpa [blockAutHom, lampEquiv_sign] using congrArg (lampEquiv hc hi).symm this

/-- The permutation of the sigma-indexed site set induced by the vertical
action. -/
def sitePerm (v : Vertical) : Equiv.Perm ((b : Block) × BlockSites b) :=
  siteEquiv.symm.trans ((MulAction.toPermHom Vertical Site v).trans siteEquiv)

/-- The vertical action permutes lamps according to `sitePerm`. -/
theorem blockAutHom_lamp (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (v : Vertical) (p : (b : Block) × BlockSites b) :
    blockAutHom hc hi v (lamp Block BlockSites p) =
      lamp Block BlockSites (sitePerm v p) := by
  have := lampAutHom_at v (siteEquiv p)
  simpa [blockAutHom, sitePerm, lampEquiv_lamp] using
    congrArg (lampEquiv hc hi).symm this

/-! ## The model as a block-Clifford tower -/

/-- The forward map of the model comparison, built from the universal property
of the semidirect product.  Mathlib has no `SemidirectProduct.congr`, so both
directions are `SemidirectProduct.lift` and the inverse is checked on
generators. -/
def toModel (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    (BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) →* Model :=
  SemidirectProduct.lift
    (SemidirectProduct.inl.comp (lampEquiv hc hi).toMonoidHom)
    SemidirectProduct.inr
    (by
      intro v
      refine MonoidHom.ext fun n ↦ ?_
      show SemidirectProduct.inl (lampEquiv hc hi (blockAutHom hc hi v n)) = _
      rw [blockAutHom]
      simp [SemidirectProduct.inl_aut, MulAut.conj_apply])

/-- **The block model is a block-Clifford semidirect product.** -/
def modelEquiv (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    (BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) ≃* Model :=
  MulEquiv.ofBijective (toModel hc hi)
    ⟨by
      intro p q hpq
      have hr : p.right = q.right := congrArg SemidirectProduct.right hpq
      have hl : lampEquiv hc hi p.left = lampEquiv hc hi q.left := by
        have := congrArg SemidirectProduct.left hpq
        simpa [toModel, hr] using this
      exact SemidirectProduct.ext ((lampEquiv hc hi).injective hl) hr,
     by
      intro m
      refine ⟨⟨(lampEquiv hc hi).symm m.left, m.right⟩, ?_⟩
      refine SemidirectProduct.ext ?_ rfl
      simp [toModel]⟩

/-- **The literal group is a block-Clifford tower.** -/
def markedGroupEquivTower (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    MarkedGroup ≃*
      (BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) :=
  markedGroupEquivModel.trans (modelEquiv hc hi).symm

/-! ## The endpoint -/

/-- **The literal group is sofic**, granted that the orbital graph is a
disjoint union of complete graphs on its blocks.

Every other input is already in the repository: residual finiteness of the
matrix base, injectivity of the doubling endomorphism, invariance of the sign,
equivariance of the lamps, and finiteness of the telescope-level orbits on the
block set. -/
theorem markedGroup_isSofic_of_completeBlocks
    (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    IsSofic MarkedGroup := by
  refine (isSofic_mulEquiv_iff (markedGroupEquivTower hc hi)).mpr ?_
  refine BlockCliffordTowerSofic.isSofic_blockClifford_tower
    (I := Block) (B := BlockSites)
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite
    LiteralNonMFLinearWitness.alpha LiteralNonMFLinearWitness.conjD_injective
    (blockAutHom hc hi)
    (fun t ↦ sitePerm (SemidirectProduct.inl t))
    (blockAutHom_sign hc hi)
    (fun t p ↦ blockAutHom_lamp hc hi (SemidirectProduct.inl t) p)
    ?_
  intro n p
  have := finite_telescopeLevel_site_orbit n (siteEquiv p)
  exact this.image siteEquiv.symm |>.subset (by
    rintro _ ⟨h, rfl⟩
    exact ⟨_, ⟨h, rfl⟩, rfl⟩)

/-- **The separation, granted the same hypothesis.**  The literal
eight-generator group is finitely presented, sofic, and not MF. -/
theorem literal_finitelyPresented_sofic_not_isCDEOperatorMF
    (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  ⟨inferInstance, markedGroup_isSofic_of_completeBlocks hc hi,
    LiteralNonMFEndpoint.literal_not_isCDEOperatorMF⟩

end

end LiteralBlockCliffordBridge
end GroupApproximation
