import GroupApproximation.Sofic.LiteralBlockNormalForm
import GroupApproximation.Sofic.BlockCliffordTowerSofic

/-!
# The lamp factor of the literal group is a block Clifford group

`Sofic/LiteralBlockNormalForm.lean` computes the literal group as
`Model = LampFactor ⋊[lampAutHom] Vertical`, where `LampFactor` is the Clifford
group of the orbital graph `𝒢`: a central sign, one involution per site, and
two lamps anticommuting through the sign exactly when their sites are
`Adjacent`.  `Sofic/BlockCliffordLamp.lean` presents `BlockClifford I B` the
same way for a *partitioned* site set: lamps anticommute exactly when they
share a block, and lamps in different blocks satisfy no relation.

The two presentations agree as soon as the orbital graph is a disjoint union
of complete graphs on the blocks.  `blockOf_eq_of_adjacent` gives one half,
that an edge stays inside a block; the other half is `IsCompleteOnBlocks`
below, that distinct sites of a block are adjacent.  Granted it, `lampEquiv`
identifies the two groups and `blockAutHom` carries the vertical action
across.

`IsCompleteOnBlocks` holds: `LiteralBlockGeometry.adj_of_blockOf_eq` derives
it from `AlphaCosetTransitive`, which
`LiteralAffineCosetTransitivity.conjD_cosetTransitive` proves over `gammaBar`.
Both are stated for `Cosets α hα` rather than for
`Site = Vertical ⧸ baseSubgroup`, so the two site types have to be identified
before that derivation can be quoted here.

The second hypothesis, `IsIrreflexive`, is smaller and reduces to distinctness
of the two marked sites by `isIrreflexive_of_siteA_ne_siteB`.
-/

namespace GroupApproximation
namespace LiteralBlockCliffordBridge

open LiteralBlockNormalForm BlockCliffordLamp

noncomputable section



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
    exact h (smul_right_injective' (g := g) (ha.trans hb.symm))
  -- at `η = ξ` the two disjuncts of `Adjacent ξ ξ` are the same statement, so
  -- both branches hand `key` its arguments in the same order
  rcases hadj with ⟨g, ha, hb⟩ | ⟨g, ha, hb⟩
  · exact key g ha hb
  · exact key g ha hb
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

@[simp] theorem genEquiv_symm_sign :
    genEquiv.symm (Sum.inl () : LampGen) = Sum.inl () := rfl

@[simp] theorem genEquiv_symm_lamp (ξ : Site) :
    genEquiv.symm (Sum.inr ξ : LampGen) = Sum.inr (siteEquiv.symm ξ) := rfl

@[simp] theorem freeEquiv_symm_of (x : LampGen) :
    freeEquiv.symm (FreeGroup.of x) = FreeGroup.of (genEquiv.symm x) := rfl

/-! ## The relator sets correspond

Both directions need one of the two graph hypotheses, and they need different
ones: sending a block braiding to a graph braiding needs completeness, and
sending a graph braiding to a block braiding needs that adjacency implies both
a common block (proved) and distinctness (irreflexivity). -/

/-- Block relators map to graph relators, given completeness. -/
theorem freeEquiv_maps_relators (hc : IsCompleteOnBlocks) :
    ∀ w ∈ relators Block BlockSites, freeEquiv w ∈ lampRelatorSet := by
  -- `braiding` keeps its block and its two sites implicit, so the pattern has
  -- to open them with `@`
  rintro w (- | p | p | @⟨b, ξ, η, hne⟩)
  · exact IsLampRelator.sign_sq
  · exact IsLampRelator.lamp_sq _
  · exact IsLampRelator.sign_comm _
  · refine IsLampRelator.braiding (hc _ _ ?_ ?_)
    · rw [blockOf_siteEquiv, blockOf_siteEquiv]
    · exact fun h ↦ hne (Subtype.ext h)

/-- Graph relators map to block relators, given irreflexivity. -/
theorem freeEquiv_symm_maps_relators (hi : IsIrreflexive) :
    ∀ w ∈ lampRelatorSet, freeEquiv.symm w ∈ relators Block BlockSites := by
  rintro w (- | ξ | ξ | @⟨ξ, η, hadj⟩)
  · exact IsRelator.sign_sq
  · exact IsRelator.lamp_sq _
  · exact IsRelator.sign_comm _
  · have hblock : blockOf ξ = blockOf η := blockOf_eq_of_adjacent hadj
    have hne : ξ ≠ η := by rintro rfl; exact hi _ hadj
    -- The goal carries `siteEquiv.symm η = ⟨blockOf η, η⟩`, while `braiding`
    -- needs both sites in *one* block.  `hblock` is exactly what re-seats the
    -- second one, and it is a propositional equality, so the seat change is a
    -- rewrite rather than unification.
    have hξ : siteEquiv.symm ξ = ⟨blockOf ξ, ⟨ξ, rfl⟩⟩ :=
      siteEquiv.symm_apply_eq.mpr rfl
    have hη : siteEquiv.symm η = ⟨blockOf ξ, ⟨η, hblock.symm⟩⟩ :=
      siteEquiv.symm_apply_eq.mpr rfl
    show IsRelator Block BlockSites _
    simp only [map_mul, map_inv, map_commutatorElement, freeEquiv_symm_of,
      genEquiv_symm_lamp, genEquiv_symm_sign, hξ, hη]
    exact IsRelator.braiding (fun h ↦ hne (congrArg Subtype.val h))

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
  -- every placeholder here is a relator set that no later argument pins down,
  -- so they are written out
  show QuotientGroup.quotientMulEquivOfEq
      (congrArg Subgroup.normalClosure (image_relators hc hi))
      (PresentedGroup.equivPresentedGroup (relators Block BlockSites) genEquiv
        (PresentedGroup.of (Sum.inl ()))) = lampSign
  rw [PresentedGroup.equivPresentedGroup_apply_of]
  rfl

@[simp] theorem lampEquiv_lamp (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (p : (b : Block) × BlockSites b) :
    lampEquiv hc hi (lamp Block BlockSites p) = lampAt (siteEquiv p) := by
  show QuotientGroup.quotientMulEquivOfEq
      (congrArg Subgroup.normalClosure (image_relators hc hi))
      (PresentedGroup.equivPresentedGroup (relators Block BlockSites) genEquiv
        (PresentedGroup.of (Sum.inr p))) = lampAt (siteEquiv p)
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
  -- both cancellations are done by hand.  `simp` proves them too, but the term
  -- it produces has to be rechecked by the kernel through `lampEquiv`, which is
  -- a composite of two quotient equivalences, and that times out.
  map_one' := by
    refine MulEquiv.ext fun n ↦ ?_
    show (lampEquiv hc hi).symm (lampAutHom 1 (lampEquiv hc hi n)) = n
    rw [map_one, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' v w := by
    refine MulEquiv.ext fun n ↦ ?_
    show (lampEquiv hc hi).symm (lampAutHom (v * w) (lampEquiv hc hi n))
      = (lampEquiv hc hi).symm (lampAutHom v (lampEquiv hc hi
          ((lampEquiv hc hi).symm (lampAutHom w (lampEquiv hc hi n)))))
    rw [MulEquiv.apply_symm_apply, map_mul, MulAut.mul_apply]

/-- The vertical action fixes the sign. -/
theorem blockAutHom_sign (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (v : Vertical) :
    blockAutHom hc hi v (sign Block BlockSites) = sign Block BlockSites := by
  show (lampEquiv hc hi).symm
      (lampAutHom v (lampEquiv hc hi (sign Block BlockSites)))
    = sign Block BlockSites
  apply (lampEquiv hc hi).injective
  rw [MulEquiv.apply_symm_apply, lampEquiv_sign, lampAutHom_sign]

/-- The permutation of the sigma-indexed site set induced by the vertical
action: transport the action along `siteEquiv`.

Read left to right, `Equiv.trans` composes forwards, so the sigma coordinate is
sent to a site, moved, and sent back. -/
def sitePerm (v : Vertical) : Equiv.Perm ((b : Block) × BlockSites b) :=
  siteEquiv.trans ((MulAction.toPermHom Vertical Site v).trans siteEquiv.symm)

@[simp] theorem sitePerm_apply (v : Vertical)
    (p : (b : Block) × BlockSites b) :
    sitePerm v p = siteEquiv.symm (v • siteEquiv p) := rfl

/-- The site permutations compose: `sitePerm` is the transport of a monoid
homomorphism along an equivalence, so it is one. -/
def sitePermHom : Vertical →* Equiv.Perm ((b : Block) × BlockSites b) where
  toFun := sitePerm
  map_one' := by
    refine Equiv.ext fun p ↦ ?_
    rw [sitePerm_apply, one_smul, Equiv.symm_apply_apply]
    rfl
  map_mul' v w := by
    refine Equiv.ext fun p ↦ ?_
    rw [sitePerm_apply]
    show siteEquiv.symm ((v * w) • siteEquiv p)
      = sitePerm v (sitePerm w p)
    rw [sitePerm_apply, sitePerm_apply, Equiv.apply_symm_apply, mul_smul]

@[simp] theorem sitePermHom_apply (v : Vertical) :
    sitePermHom v = sitePerm v := rfl

/-- The vertical action permutes lamps according to `sitePerm`. -/
theorem blockAutHom_lamp (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (v : Vertical) (p : (b : Block) × BlockSites b) :
    blockAutHom hc hi v (lamp Block BlockSites p) =
      lamp Block BlockSites (sitePerm v p) := by
  show (lampEquiv hc hi).symm
      (lampAutHom v (lampEquiv hc hi (lamp Block BlockSites p)))
    = lamp Block BlockSites (sitePerm v p)
  apply (lampEquiv hc hi).injective
  rw [MulEquiv.apply_symm_apply, lampEquiv_lamp, lampAutHom_at, lampEquiv_lamp,
    sitePerm_apply, Equiv.apply_symm_apply]

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
      -- `blockAutHom` conjugates, so the outer `lampEquiv` cancels the inner
      -- `lampEquiv.symm` and what is left is the defining relation of the
      -- semidirect product
      rw [show lampEquiv hc hi (blockAutHom hc hi v n)
            = lampAutHom v (lampEquiv hc hi n) from
          (lampEquiv hc hi).apply_symm_apply _]
      simp [SemidirectProduct.inl_aut, MulAut.conj_apply])

@[simp] theorem toModel_left (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (r : BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) :
    (toModel hc hi r).left = lampEquiv hc hi r.left := by
  show (SemidirectProduct.inl (lampEquiv hc hi r.left) *
      SemidirectProduct.inr r.right).left = lampEquiv hc hi r.left
  simp

@[simp] theorem toModel_right (hc : IsCompleteOnBlocks) (hi : IsIrreflexive)
    (r : BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) :
    (toModel hc hi r).right = r.right := by
  show (SemidirectProduct.inl (lampEquiv hc hi r.left) *
      SemidirectProduct.inr r.right).right = r.right
  simp

/-- **The block model is a block-Clifford semidirect product.** -/
def modelEquiv (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    (BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) ≃* Model :=
  MulEquiv.ofBijective (toModel hc hi)
    ⟨by
      intro p q hpq
      have hr : p.right = q.right := by
        simpa using congrArg SemidirectProduct.right hpq
      have hl : lampEquiv hc hi p.left = lampEquiv hc hi q.left := by
        simpa using congrArg SemidirectProduct.left hpq
      exact SemidirectProduct.ext ((lampEquiv hc hi).injective hl) hr,
     by
      intro m
      refine ⟨⟨(lampEquiv hc hi).symm m.left, m.right⟩, ?_⟩
      refine SemidirectProduct.ext ?_ ?_
      · simp
      · simp⟩

/-- **The literal group is a block-Clifford tower.** -/
def markedGroupEquivTower (hc : IsCompleteOnBlocks) (hi : IsIrreflexive) :
    LiteralNonMFPresentation.MarkedGroup ≃*
      (BlockClifford Block BlockSites ⋊[blockAutHom hc hi] Vertical) :=
  markedGroupEquivModel.trans (modelEquiv hc hi).symm

/-! ## Equivariance of the block subgroups

The one field of `LiteralTelescopeCoreLEF.TelescopeCoreData` that no lane
claimed: it is the bridge between the amalgam lane's block *subgroups* and the
block lane's block *permutations*.  It needs neither, in fact — it is a
closure argument from two facts that are already proved, that the action
permutes the site lamps (`LiteralLampKernelSplit.sect_conj_siteLamp`) and that
it permutes the blocks compatibly (`LiteralBlockNormalForm.blockOf_smul`).

Stated here for `Subgroup.closure (c '' {ξ | blockOf ξ = i})`, which is the
body of the amalgam lane's `blockGroupOf`, so that this module does not depend
on that one. -/

/-- **The block subgroups are equivariant.**  If an action permutes the site
family the way the vertical group permutes sites, then it carries the subgroup
generated by a block onto the subgroup generated by the image block. -/
theorem closure_block_equivariant {N : Type} [Group N] (c : Site → N)
    (φ : Vertical →* MulAut N)
    (hc : ∀ (v : Vertical) (ξ : Site), φ v (c ξ) = c (v • ξ))
    (v : Vertical) (i : Block) :
    ∀ x ∈ Subgroup.closure (c '' {ξ : Site | blockOf ξ = i}),
      φ v x ∈ Subgroup.closure (c '' {ξ : Site | blockOf ξ = v • i}) := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨ξ, hξ, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨v • ξ, ?_, (hc v ξ).symm ▸ rfl⟩
      show blockOf (v • ξ) = v • i
      rw [blockOf_smul, hξ]
  | one => simp
  | mul y z _ _ hy hz => simpa [map_mul] using Subgroup.mul_mem _ hy hz
  | inv y _ hy => simpa [map_inv] using Subgroup.inv_mem _ hy

/-! ## The endpoint -/

/-! ## Not here: the passage to soficity

Applying `BlockCliffordTowerSofic.isSofic_blockClifford_tower` to the model
above would need its `Vertical` to be `MarkedCompression.Vertical`, the
telescope, while the `Vertical` of this file is `PresentedGroup
verticalRelators`.  The two are unrelated types.

The passage is made instead over the telescope throughout, where
`LiteralLampKernelSplit.markedGroupEquivSemidirect` presents the literal
group as `lampKernel ⋊ V`, `LiteralLampKernelSplit.cosetLamp` indexes lamps
by `Cosets alpha conjD_injective`, `LiteralBlockGeometry` states the block
geometry over that same site type, and `LiteralLampKernelAmalgam` is
parameterized in `Block`, `Site`, `blockOf` and the ambient group, so it
instantiates at `N := lampKernel`, `c := cosetLamp`. -/

end

end LiteralBlockCliffordBridge
end GroupApproximation
