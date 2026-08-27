import GroupApproximation.Sofic.LiteralBlockNormalForm
import GroupApproximation.Sofic.LiteralLampKernelSplit
import GroupApproximation.Sofic.LiteralBlockGeometry

/-!
# The two vertical groups of the literal development are the same group

The literal forty-one-relator group `E` is analysed in this repository along
two lanes that never meet:

* `Sofic/LiteralBlockNormalForm.lean` computes `E ≅ C(𝒢) ⋊ Vertical` with
  `Vertical = PresentedGroup verticalRelators` the seven-letter presented
  quotient `E/⟨⟨c⟩⟩`, and develops sites, blocks, the orbital graph and the
  finite telescope-level orbits over that carrier;
* `Sofic/LiteralLampKernelSplit.lean` computes `E ≅ N_E ⋊ V` with
  `V = Vertical alpha conjD_injective` the *ascending HNN extension of the
  matrix base* `Γ̄`, and re-associates it to `E ≅ (N_E ⋊ T) ⋊ ℤ`, which is the
  shape the soficity endpoint consumes.

`Sofic/LiteralBlockCliffordBridge.lean` records the consequence of their being
unrelated types: "the passage is made instead over the telescope throughout".
This file removes the obstruction rather than working around it.

## Why the two carriers are the same

Both are the quotient of `E` by the normal closure of the lamp letter, and
both lanes prove it:

* `LiteralBlockNormalForm.lampKernel_eq : lampKernel = ker retract`;
* `LiteralLampKernelSplit.lampKernel_eq_ker : lampKernel = ker retraction`.

The two `lampKernel`s are *the same subgroup on the nose* — each is
`Subgroup.normalClosure {lamp}` in `MarkedGroup`, so `lampKernel_agree` is
`rfl`.  Both retractions are surjective, so the first isomorphism theorem
identifies the two carriers.

The isomorphism is not built through the quotient, though: both lanes already
carry a section (`LiteralBlockNormalForm.verticalToE` and
`LiteralLampKernelSplit.sect`), so the two directions are the honest composites

    toV   = retraction ∘ verticalToE ,
    fromV = retract    ∘ sect ,

and the round trips are checked on generators.  That keeps every statement
below computable in terms the two lanes already state, rather than in terms of
`QuotientGroup.kerLift`.

## What this buys

The geometry lane `Sofic/LiteralBlockGeometry.lean` and the transitivity
theorem `LiteralAffineCosetTransitivity.conjD_cosetTransitive` are stated over
`Cosets alpha conjD_injective`, i.e. over `V`.  The presentation lane's two
open graph hypotheses — `LiteralBlockCliffordBridge.IsCompleteOnBlocks` and
`IsIrreflexive` — are stated over `LiteralBlockNormalForm.Site`.  With the
identification below the first pair discharges the second, which is the whole
of the remaining trust surface of the soficity chain.

Nothing here is analysis and nothing here is new mathematics: it is the
statement that two names for `E/⟨⟨c⟩⟩` denote one group.
-/

namespace GroupApproximation
namespace LiteralVerticalBridge

open LiteralNonMFPresentation

noncomputable section

/-! ## The two lamp kernels, and the two retractions -/

/-- **The two lanes' lamp kernels are the same subgroup.**  Both are defined
as `Subgroup.normalClosure {lamp}` inside `MarkedGroup`. -/
@[simp] theorem lampKernel_agree :
    LiteralBlockNormalForm.lampKernel = LiteralLampKernelSplit.lampKernel := rfl

/-- **The two retractions have the same kernel.** -/
theorem ker_agree :
    MonoidHom.ker LiteralBlockNormalForm.retract
      = MonoidHom.ker LiteralLampKernelSplit.retraction := by
  rw [← LiteralBlockNormalForm.lampKernel_eq, lampKernel_agree,
    LiteralLampKernelSplit.lampKernel_eq_ker]

/-- The presented vertical retraction is surjective: it fixes every generator
of the presented target. -/
theorem retract_surjective :
    Function.Surjective LiteralBlockNormalForm.retract := by
  rw [← MonoidHom.range_eq_top]
  refine eq_top_iff.mpr ?_
  rw [← PresentedGroup.closure_range_of
    (rels := LiteralBlockNormalForm.verticalRelators)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨PresentedGroup.of j, LiteralBlockNormalForm.retract_of j⟩

/-! ## The comparison maps

Both directions are composites of maps the two lanes already build. -/

/-- From the presented vertical group to the matrix-base HNN extension. -/
def toV : LiteralBlockNormalForm.Vertical →* LiteralLampKernelSplit.V :=
  LiteralLampKernelSplit.retraction.comp LiteralBlockNormalForm.verticalToE

/-- From the matrix-base HNN extension to the presented vertical group. -/
def fromV : LiteralLampKernelSplit.V →* LiteralBlockNormalForm.Vertical :=
  LiteralBlockNormalForm.retract.comp LiteralLampKernelSplit.sect

/-- **`toV` intertwines the two retractions.**  Checked on the eight letters:
on a base letter and on the stable letter both sides are the retraction of
that letter, and on the lamp letter both sides are `1`, because
`verticalToE` sends the lamp generator of the *vertical* group nowhere — the
lamp letter of `E` retracts to `1` first. -/
theorem toV_comp_retract :
    toV.comp LiteralBlockNormalForm.retract = LiteralLampKernelSplit.retraction := by
  refine PresentedGroup.ext ?_
  intro j
  rw [MonoidHom.comp_apply, LiteralBlockNormalForm.retract_of, toV,
    MonoidHom.comp_apply, LiteralBlockNormalForm.verticalToE_of]
  -- Goal: `retraction (eGen j) = retraction (PresentedGroup.of j)`.
  -- On a base letter and on the stable letter `eGen j` *is* the letter; on the
  -- lamp letter `eGen` gives `1` and `retraction` kills the letter anyway.
  rcases j with i | k
  · rfl
  · fin_cases k
    · simp [LiteralBlockNormalForm.eGen, LiteralBlockNormalForm.of_stable_eq]
    · simp [LiteralBlockNormalForm.eGen, LiteralBlockNormalForm.of_lamp_eq,
        LiteralLampKernelSplit.retraction_lamp]

theorem toV_retract (g : MarkedGroup) :
    toV (LiteralBlockNormalForm.retract g) = LiteralLampKernelSplit.retraction g :=
  DFunLike.congr_fun toV_comp_retract g

/-- **`fromV` intertwines the two retractions the other way.**  `sect` is a
section of `retraction`, so `fromV ∘ retraction` collapses the lamp kernel,
which `retract` already does. -/
theorem fromV_retraction (g : MarkedGroup) :
    fromV (LiteralLampKernelSplit.retraction g)
      = LiteralBlockNormalForm.retract g := by
  -- `sect (retraction g)` differs from `g` by a lamp-kernel element, and the
  -- presented retraction kills the lamp kernel.
  have hmem : g⁻¹ * LiteralLampKernelSplit.sect
      (LiteralLampKernelSplit.retraction g) ∈ LiteralLampKernelSplit.lampKernel := by
    rw [LiteralLampKernelSplit.mem_lampKernel_iff, map_mul, map_inv,
      LiteralLampKernelSplit.retraction_sect, inv_mul_cancel]
  have hker : g⁻¹ * LiteralLampKernelSplit.sect
      (LiteralLampKernelSplit.retraction g)
      ∈ MonoidHom.ker LiteralBlockNormalForm.retract := by
    rw [← LiteralBlockNormalForm.lampKernel_eq, lampKernel_agree]
    exact hmem
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hker
  show LiteralBlockNormalForm.retract (LiteralLampKernelSplit.sect
    (LiteralLampKernelSplit.retraction g)) = LiteralBlockNormalForm.retract g
  exact hker.symm

/-! ## The isomorphism -/

theorem fromV_comp_toV :
    fromV.comp toV = MonoidHom.id LiteralBlockNormalForm.Vertical := by
  refine PresentedGroup.ext ?_
  intro j
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  have hj : LiteralBlockNormalForm.retract (PresentedGroup.of j)
      = (PresentedGroup.of j : LiteralBlockNormalForm.Vertical) :=
    LiteralBlockNormalForm.retract_of j
  calc fromV (toV (PresentedGroup.of j))
      = fromV (toV (LiteralBlockNormalForm.retract (PresentedGroup.of j))) := by
        rw [hj]
    _ = fromV (LiteralLampKernelSplit.retraction (PresentedGroup.of j)) := by
        rw [toV_retract]
    _ = LiteralBlockNormalForm.retract (PresentedGroup.of j) := by
        rw [fromV_retraction]
    _ = PresentedGroup.of j := hj

theorem toV_comp_fromV :
    toV.comp fromV = MonoidHom.id LiteralLampKernelSplit.V := by
  refine MonoidHom.ext fun v ↦ ?_
  obtain ⟨g, rfl⟩ := LiteralLampKernelSplit.retraction_surjective v
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, fromV_retraction, toV_retract]

/-- **The two vertical groups are the same group.** -/
def verticalEquiv :
    LiteralBlockNormalForm.Vertical ≃* LiteralLampKernelSplit.V where
  toFun := toV
  invFun := fromV
  left_inv v := DFunLike.congr_fun fromV_comp_toV v
  right_inv v := DFunLike.congr_fun toV_comp_fromV v
  map_mul' := toV.map_mul

@[simp] theorem verticalEquiv_apply (v : LiteralBlockNormalForm.Vertical) :
    verticalEquiv v = toV v := rfl

@[simp] theorem verticalEquiv_symm_apply (v : LiteralLampKernelSplit.V) :
    verticalEquiv.symm v = fromV v := rfl

theorem verticalEquiv_retract (g : MarkedGroup) :
    verticalEquiv (LiteralBlockNormalForm.retract g)
      = LiteralLampKernelSplit.retraction g :=
  toV_retract g

/-! ## The base subgroups correspond

`LiteralBlockNormalForm.baseSubgroup` is `verticalBase.range` with
`verticalBase = retract ∘ baseMap`; the site set of the split lane is the
coset space of `(iotaVertical alpha conjD_injective).range`.  The two agree
because `retraction ∘ baseMap = iotaVertical ∘ affineQuotient`
(`LiteralLampKernelSplit.retraction_comp_baseMap`) and `affineQuotient` is
surjective — that surjectivity is the easy half of
`LiteralBaseCompleteness.baseAffineEquiv`, and is the only place the base
completeness theorem is used in this file. -/

theorem toV_verticalBase (u : LiteralNonMFPresentation.Base) :
    toV (LiteralBlockNormalForm.verticalBase u)
      = MarkedCompression.iotaVertical LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective
          (LiteralBaseAffineQuotient.affineQuotient u) := by
  rw [LiteralBlockNormalForm.verticalBase, MonoidHom.comp_apply, toV_retract,
    LiteralLampKernelSplit.retraction_baseMap]

/-- **The base subgroup maps onto the level-zero copy of the matrix base.** -/
theorem map_baseSubgroup :
    Subgroup.map verticalEquiv.toMonoidHom LiteralBlockNormalForm.baseSubgroup
      = (MarkedCompression.iotaVertical LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective).range := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨LiteralBaseAffineQuotient.affineQuotient u,
      (toV_verticalBase u).symm ▸ rfl⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨u, rfl⟩ := LiteralBaseAffineQuotient.affineQuotient_surjective γ
    exact ⟨LiteralBlockNormalForm.verticalBase u, ⟨u, rfl⟩, toV_verticalBase u⟩

/-! ## The site sets correspond

`LiteralBlockNormalForm.Site = Vertical ⧸ baseSubgroup` and
`MarkedCompression.Cosets = V ⧸ (iotaVertical).range` are coset spaces of
non-normal subgroups, so this is an `Equiv`, not a `MulEquiv`; it is
equivariant along `verticalEquiv`, which is all the geometry lane needs. -/

/-- **The two site sets are the same set**, compatibly with the two actions. -/
def siteEquiv :
    LiteralBlockNormalForm.Site ≃
      MarkedCompression.Cosets LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective := by
  refine Quotient.congr verticalEquiv.toEquiv ?_
  intro a b
  dsimp
  rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq, QuotientGroup.eq]
  constructor
  · intro h
    have hmap : verticalEquiv (a⁻¹ * b)
        ∈ Subgroup.map verticalEquiv.toMonoidHom
            LiteralBlockNormalForm.baseSubgroup :=
      Subgroup.mem_map_of_mem _ h
    rw [map_baseSubgroup, map_mul, map_inv] at hmap
    exact hmap
  · intro h
    have hmap : verticalEquiv (a⁻¹ * b)
        ∈ Subgroup.map verticalEquiv.toMonoidHom
            LiteralBlockNormalForm.baseSubgroup := by
      rw [map_baseSubgroup, map_mul, map_inv]
      exact h
    obtain ⟨u, hu, hue⟩ := hmap
    rwa [← verticalEquiv.injective hue]

@[simp] theorem siteEquiv_mk (g : LiteralBlockNormalForm.Vertical) :
    siteEquiv (QuotientGroup.mk g) = QuotientGroup.mk (verticalEquiv g) := rfl

/-- The site identification is equivariant. -/
theorem siteEquiv_smul (v : LiteralBlockNormalForm.Vertical)
    (ξ : LiteralBlockNormalForm.Site) :
    siteEquiv (v • ξ) = verticalEquiv v • siteEquiv ξ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ξ
  rw [LiteralBlockNormalForm.smul_mk, siteEquiv_mk, siteEquiv_mk,
    MulAction.Quotient.smul_mk, smul_eq_mul, map_mul]

/-! ## The marked pair corresponds -/

theorem toV_vStable :
    toV LiteralBlockNormalForm.vStable
      = MarkedCompression.tVertical LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective := by
  rw [toV, MonoidHom.comp_apply, LiteralBlockNormalForm.verticalToE_vStable,
    LiteralLampKernelSplit.retraction_stable]

theorem toV_vV1 :
    toV LiteralBlockNormalForm.vV1
      = MarkedCompression.iotaVertical LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective ExplicitLinearModel.v1G := by
  rw [toV, MonoidHom.comp_apply, LiteralBlockNormalForm.verticalToE_vV1,
    LiteralLampKernelSplit.retraction_base_generator,
    LiteralNonMFLinearWitness.matrixBaseGenerator_v1]

theorem siteEquiv_siteA :
    siteEquiv LiteralBlockNormalForm.siteA
      = LiteralBlockGeometry.markedSiteA LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective := by
  rw [LiteralBlockNormalForm.siteA, siteEquiv_mk, verticalEquiv_apply,
    toV_vStable, LiteralBlockGeometry.markedSiteA_eq_mk]

theorem siteEquiv_siteB :
    siteEquiv LiteralBlockNormalForm.siteB
      = LiteralBlockGeometry.markedSiteB LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective ExplicitLinearModel.v1G := by
  rw [LiteralBlockNormalForm.siteB, siteEquiv_mk, verticalEquiv_apply, map_mul,
    toV_vV1, toV_vStable, LiteralBlockGeometry.markedSiteB_eq_mk]

/-- **The two orbital graphs are the same graph.**  Both are the orbit of the
marked pair under the vertical group, and the marked pairs correspond. -/
theorem adjacent_iff (ξ η : LiteralBlockNormalForm.Site) :
    LiteralBlockNormalForm.Adjacent ξ η ↔
      LiteralBlockGeometry.Adj LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective ExplicitLinearModel.v1G
        (siteEquiv ξ) (siteEquiv η) := by
  constructor
  · rintro (⟨g, hga, hgb⟩ | ⟨g, hga, hgb⟩)
    · refine ⟨verticalEquiv g, Or.inl ⟨?_, ?_⟩⟩
      · rw [← siteEquiv_siteA, ← siteEquiv_smul, hga]
      · rw [← siteEquiv_siteB, ← siteEquiv_smul, hgb]
    · refine ⟨verticalEquiv g, Or.inr ⟨?_, ?_⟩⟩
      · rw [← siteEquiv_siteA, ← siteEquiv_smul, hga]
      · rw [← siteEquiv_siteB, ← siteEquiv_smul, hgb]
  · rintro ⟨v, hv | hv⟩
    · obtain ⟨g, rfl⟩ := verticalEquiv.surjective v
      refine Or.inl ⟨g, ?_, ?_⟩
      · exact siteEquiv.injective (by
          rw [siteEquiv_smul, siteEquiv_siteA]; exact hv.1)
      · exact siteEquiv.injective (by
          rw [siteEquiv_smul, siteEquiv_siteB]; exact hv.2)
    · obtain ⟨g, rfl⟩ := verticalEquiv.surjective v
      refine Or.inr ⟨g, ?_, ?_⟩
      · exact siteEquiv.injective (by
          rw [siteEquiv_smul, siteEquiv_siteA]; exact hv.1)
      · exact siteEquiv.injective (by
          rw [siteEquiv_smul, siteEquiv_siteB]; exact hv.2)

/-! ## Blocks refine

`LiteralBlockNormalForm.blockSubgroup = ⟨B, β⟩` is contained in the geometry
lane's `blockSubgroup = B₁ = τ⁻¹Bτ`, so the presented blocks *refine* the
geometric ones.  Only this inclusion is needed: it is what turns "distinct
sites of a geometric block are adjacent" into "distinct sites of a presented
block are adjacent".  The reverse inclusion is true — the `B`-conjugates of
`β` fill `B₁/B` by the same transitivity — but proving it is unnecessary, and
the two hypotheses together force it a posteriori. -/

theorem map_blockSubgroup_le :
    Subgroup.map verticalEquiv.toMonoidHom LiteralBlockNormalForm.blockSubgroup
      ≤ LiteralBlockGeometry.blockSubgroup LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective := by
  rw [LiteralBlockNormalForm.blockSubgroup, Subgroup.map_sup, sup_le_iff]
  constructor
  · rw [map_baseSubgroup]
    exact LiteralBlockGeometry.baseSubgroup_le_blockSubgroup _ _
  · rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨y, rfl, rfl⟩
    refine (LiteralBlockGeometry.mem_blockSubgroup_iff _ _ _).mpr
      ⟨ExplicitLinearModel.v1G, ?_⟩
    show _ = toV (LiteralBlockNormalForm.vStable⁻¹ *
      LiteralBlockNormalForm.vV1 * LiteralBlockNormalForm.vStable)
    rw [map_mul, map_mul, map_inv, toV_vStable, toV_vV1]

/-- **Presented blocks refine geometric blocks.** -/
theorem blockOf_eq_of_blockOf_eq {ξ η : LiteralBlockNormalForm.Site}
    (h : LiteralBlockNormalForm.blockOf ξ = LiteralBlockNormalForm.blockOf η) :
    LiteralBlockGeometry.blockOf LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective (siteEquiv ξ)
      = LiteralBlockGeometry.blockOf LiteralNonMFLinearWitness.alpha
          ExplicitLinearModel.conjD_injective (siteEquiv η) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ξ
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective η
  rw [LiteralBlockNormalForm.blockOf_mk, LiteralBlockNormalForm.blockOf_mk,
    QuotientGroup.eq] at h
  rw [siteEquiv_mk, siteEquiv_mk, LiteralBlockGeometry.blockOf_mk,
    LiteralBlockGeometry.blockOf_mk, QuotientGroup.eq]
  have hmap : verticalEquiv (a⁻¹ * b)
      ∈ Subgroup.map verticalEquiv.toMonoidHom
          LiteralBlockNormalForm.blockSubgroup :=
    Subgroup.mem_map_of_mem _ h
  have := map_blockSubgroup_le hmap
  simpa only [map_mul, map_inv] using this

end

end LiteralVerticalBridge
end GroupApproximation
