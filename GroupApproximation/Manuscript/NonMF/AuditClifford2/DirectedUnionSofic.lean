import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.SoficDirectedUnion
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# The Clifford witness `W` is sofic

`non_mf_groups_exist.tex`, proof of `prop:clifford-locally-rf`, lines 2047--2053:

> Therefore every finitely generated subgroup of $W_0$ is residually finite,
> hence sofic.  The group $W_0$ is their directed union, and
> $W/W_0\cong\mathbb Z$ is amenable.  Soficity passes to directed unions and to
> extensions with amenable quotient~\cite[Theorem~1]{ElekSzabo}, so $W$ is
> sofic.

In the corpus `W = Ambient α hα`. The shift kernel `W_0` is
`ShiftKernelFor α hα = C(X) ⋊ T_α`, and
`ambientEquivShiftKernelForByInt : W ≃* W_0 ⋊ ℤ` reassociates `W`.

Proof route.
* A finitely generated subgroup of `W_0` is residually finite
  (`shiftKernelFor_isLocallyResiduallyFinite`), hence LEF, hence sofic
  (`isLEF_of_residuallyFinite`, `isSofic_of_isLEF`).
* Directed union: every finite subset of `W_0` lies in the finitely generated
  subgroup it generates, and finitely generated subgroups are closed under `⊔`.
  Inside `W`, `W_0` is the kernel of the height map `W → ℤ`; that map is
  surjective, so `W / W_0 ≅ ℤ`, and `ℤ` is amenable (`isAmenable_int`).
* Permanence: soficity passes to directed unions
  (`isSofic_of_every_finset_mem_sofic_subgroup`) and to extensions with amenable
  quotient (`manuscriptSoficOfSoficKerOfAmenableQuotient`), both stated for
  arbitrary groups. So `W_0` is sofic, and `W ≅ W_0 ⋊ ℤ` is sofic
  (`isSofic_semidirectProduct`, `isSofic_mulEquiv_iff`).
-/

namespace GroupApproximation.Manuscript.NonMF.AuditClifford2

open MappingTelescope MarkedCompression CliffordWitnessLocallyRFByInt SemidirectProduct

noncomputable section

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- tex 2047--2048: every finitely generated subgroup of `W_0` is residually
finite, hence sofic. -/
theorem manuscriptSentence_fgSubgroupsResiduallyFiniteSofic [Group.ResiduallyFinite Γ]
    [α.range.FiniteIndex] :
    ∀ H : Subgroup (ShiftKernelFor α hα), H.FG →
      Group.ResiduallyFinite H ∧ IsSofic H := by
  intro H hH
  haveI : Group.ResiduallyFinite H := shiftKernelFor_isLocallyResiduallyFinite α hα H hH
  exact ⟨inferInstance, isSofic_of_isLEF isLEF_of_residuallyFinite⟩

#audit_axioms manuscriptSentence_fgSubgroupsResiduallyFiniteSofic

/-- The height map `W → ℤ`, read through the reassociation `W ≅ W_0 ⋊ ℤ`. -/
abbrev shiftQuotientHom : Ambient α hα →* Multiplicative ℤ :=
  (SemidirectProduct.rightHom :
      ShiftKernelFor α hα ⋊[shiftActionFor α hα] Multiplicative ℤ →* Multiplicative ℤ).comp
    (ambientEquivShiftKernelForByInt α hα).toMonoidHom

/-- `W_0` as a normal subgroup of `W`. -/
abbrev shiftKernelSubgroup : Subgroup (Ambient α hα) := (shiftQuotientHom α hα).ker

theorem shiftQuotientHom_surjective : Function.Surjective (shiftQuotientHom α hα) := by
  intro z
  obtain ⟨p, hp⟩ := SemidirectProduct.rightHom_surjective (φ := shiftActionFor α hα) z
  refine ⟨(ambientEquivShiftKernelForByInt α hα).symm p, ?_⟩
  show SemidirectProduct.rightHom ((ambientEquivShiftKernelForByInt α hα)
    ((ambientEquivShiftKernelForByInt α hα).symm p)) = z
  rw [MulEquiv.apply_symm_apply]
  exact hp

/-- tex 2048--2049:
* `W_0` is the directed union of its finitely generated subgroups: every finite
  subset lies in one, and any two lie in a common one;
* inside `W`, `W_0` is the kernel of the height map;
* `W / W_0 ≅ ℤ`;
* `W / W_0` is amenable. -/
theorem manuscriptSentence_directedUnionQuotientInt :
    (∀ F : Finset (ShiftKernelFor α hα),
        ∃ H : Subgroup (ShiftKernelFor α hα), H.FG ∧ ∀ g ∈ F, g ∈ H) ∧
      (∀ H K : Subgroup (ShiftKernelFor α hα), H.FG → K.FG → (H ⊔ K).FG) ∧
      (∀ w : Ambient α hα, w ∈ shiftKernelSubgroup α hα ↔
        ∃ k : ShiftKernelFor α hα, ambientEquivShiftKernelForByInt α hα w = inl k) ∧
      Nonempty (Ambient α hα ⧸ shiftKernelSubgroup α hα ≃* Multiplicative ℤ) ∧
      Amenability.IsAmenable (Ambient α hα ⧸ shiftKernelSubgroup α hα) := by
  refine ⟨fun F ↦ ⟨Subgroup.closure (F : Set (ShiftKernelFor α hα)), ⟨F, rfl⟩,
      fun _ hg ↦ Subgroup.subset_closure (Finset.mem_coe.mpr hg)⟩,
    fun _ _ hH hK ↦ hH.sup hK, fun w ↦ ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective (shiftQuotientHom α hα)
      (shiftQuotientHom_surjective α hα)⟩,
    SoficByAmenablePermanence.isAmenable_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective (shiftQuotientHom α hα)
        (shiftQuotientHom_surjective α hα))
      SoficByAmenablePermanence.isAmenable_int⟩
  constructor
  · intro hw
    have hr : ((ambientEquivShiftKernelForByInt α hα) w).right = 1 := MonoidHom.mem_ker.mp hw
    exact ⟨((ambientEquivShiftKernelForByInt α hα) w).left, SemidirectProduct.ext rfl hr⟩
  · rintro ⟨k, hk⟩
    refine MonoidHom.mem_ker.mpr ?_
    show ((ambientEquivShiftKernelForByInt α hα) w).right = 1
    rw [hk, SemidirectProduct.right_inl]

#audit_axioms manuscriptSentence_directedUnionQuotientInt

/-- tex 2050--2053:
* soficity passes to directed unions (for an arbitrary group, if every finite
  subset lies in a sofic subgroup, the group is sofic);
* soficity passes to extensions with amenable quotient;
* hence `W_0` is sofic, and `W` is sofic. -/
theorem manuscriptSentence_soficDirectedUnionAmenableExtension [Group.ResiduallyFinite Γ]
    [α.range.FiniteIndex] :
    (∀ (G : Type) [Group G],
        (∀ F : Finset G, ∃ K : Subgroup G, IsSofic K ∧ ∀ g ∈ F, g ∈ K) → IsSofic G) ∧
      (∀ (G Q : Type) [Group G] [Group Q] (f : G →* Q),
        Function.Surjective f → IsSofic f.ker → Amenability.IsAmenable Q → IsSofic G) ∧
      IsSofic (ShiftKernelFor α hα) ∧ IsSofic (Ambient α hα) := by
  have hK : IsSofic (ShiftKernelFor α hα) :=
    isSofic_of_every_finset_mem_sofic_subgroup fun F ↦
      ⟨Subgroup.closure (F : Set (ShiftKernelFor α hα)),
        (manuscriptSentence_fgSubgroupsResiduallyFiniteSofic α hα
          (Subgroup.closure (F : Set (ShiftKernelFor α hα))) ⟨F, rfl⟩).2,
        fun _ hg ↦ Subgroup.subset_closure (Finset.mem_coe.mpr hg)⟩
  refine ⟨?_, ?_, hK, ?_⟩
  · intro G _ h
    exact isSofic_of_every_finset_mem_sofic_subgroup h
  · intro G Q _ _ f hf hker hQ
    exact SoficByAmenablePermanence.manuscriptSoficOfSoficKerOfAmenableQuotient f hf hker hQ
  · exact (isSofic_mulEquiv_iff (ambientEquivShiftKernelForByInt α hα)).mpr
      (SoficByAmenablePermanence.isSofic_semidirectProduct (shiftActionFor α hα) hK
        SoficByAmenablePermanence.isAmenable_int)

#audit_axioms manuscriptSentence_soficDirectedUnionAmenableExtension

end

end GroupApproximation.Manuscript.NonMF.AuditClifford2
