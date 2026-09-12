import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.SoficDirectedUnion
import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Criterion.CriterionAssembly
import GroupApproximation.Leavitt.ThompsonVWitness
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Finset.Order

/-!
# Printed citation sentences on soficity: Elek--Szabó, Kun, Kun--Thom

`non_mf_groups_exist.tex` cites Elek--Szabó [ES, Theorem 1] twice (lines 262 and 1568), and
Kun [Ku16] and Kun--Thom [KT19] once each (line 328).  This module gives each of these printed
sentences a closed carrier at the generality of the printed text: a named `Prop` together with
its proof.  Every result the sentences use is proved in the repository, with no literature
input:

* Elek--Szabó, Theorem 1 (soficity passes to extensions with amenable quotient) is
  `SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable`, proved from Følner sets;
* locally residually finite groups are sofic: `isSofic_of_locallyResiduallyFinite`;
* soficity passes to directed unions: `isSofic_of_directedUnion` below, over
  `isSofic_of_every_finset_mem_sofic_subgroup`;
* the rigidity step of the compression criterion (soficity and property (T) force the
  centralizing subgroup to be LEF) is `isLEF_of_isSofic`, from the Kun fixed decomposition;
* Thompson's group `V` is not LEF: `BinaryLeavitt.thompsonV_not_isLEF`.
-/

namespace GroupApproximation
namespace SoficCitationSentences

open LocallyRFByIntAmenableTrace CliffordWitnessLocallyRFByInt MarkedCompression
open LiteralNonMFLinearWitness

/-! ## Directed unions -/

/-- **Soficity passes to directed unions.**  If `G` is the union of a directed family of sofic
subgroups, then `G` is sofic. -/
theorem isSofic_of_directedUnion {G : Type*} [Group G] {ι : Type*}
    (H : ι → Subgroup G) (hdir : Directed (· ≤ ·) H)
    (hH : ∀ i, IsSofic (H i)) (hcover : ∀ g : G, ∃ i, g ∈ H i) :
    IsSofic G := by
  classical
  obtain ⟨i₀, -⟩ := hcover 1
  haveI : Nonempty ι := ⟨i₀⟩
  choose idx hidx using hcover
  apply isSofic_of_every_finset_mem_sofic_subgroup
  intro F
  obtain ⟨z, hz⟩ := hdir.finset_le (F.image idx)
  refine ⟨H z, hH z, fun g hg => ?_⟩
  have hle : H (idx g) ≤ H z := hz (idx g) (Finset.mem_image_of_mem idx hg)
  exact hle (hidx g)

/-! ## `thm:amenable-trace`, introduction (tex lines 260--262) -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:260-262`, after `thm:amenable-trace`).

> The group $W$ is sofic because locally residually finite groups are sofic and soficity passes
> to extensions with amenable quotient~\cite[Theorem~1]{ElekSzabo}.

The carrier has five conjuncts: locally residually finite groups are sofic; soficity passes to
extensions with amenable quotient (Elek--Szabó, Theorem 1, at printed generality); the shift
kernel `W₀` of the explicit affine--Clifford witness `W = WitnessGroup` is locally residually
finite; `W ≅ W₀ ⋊ ℤ`; and `W` is sofic. -/
def PrintedIntroWSoficMechanism : Prop :=
  (∀ (K : Type) [Group K], IsLocallyResiduallyFinite K → IsSofic K) ∧
  (∀ (G Q : Type) [Group G] [Group Q] (f : G →* Q),
    Function.Surjective f → IsSofic f.ker → Amenability.IsAmenable Q → IsSofic G) ∧
  IsLocallyResiduallyFinite ShiftKernel ∧
  Nonempty (WitnessGroup ≃* (ShiftKernel ⋊[shiftAction] Multiplicative ℤ)) ∧
  IsSofic WitnessGroup

theorem printedIntroWSoficMechanism : PrintedIntroWSoficMechanism := by
  refine ⟨?_, ?_, shiftKernel_isLocallyResiduallyFinite,
    ⟨witnessGroupEquivShiftKernelByInt⟩, ?_⟩
  · intro K _ hK
    exact isSofic_of_locallyResiduallyFinite hK
  · intro G Q _ _ f hf hker hQ
    exact SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable f hf hker hQ
  · exact (isSofic_mulEquiv_iff witnessGroupEquivShiftKernelByInt).mpr
      (SoficByAmenablePermanence.isSofic_int_semidirectProduct shiftAction
        (isSofic_of_locallyResiduallyFinite shiftKernel_isLocallyResiduallyFinite))

/-! ## `prop:clifford-locally-rf`, proof (tex lines 1566--1568) -/

/-- Every finite subset of the shift kernel `W₀` lies in a finitely generated subgroup, which is
residually finite and hence sofic.  So `W₀` is the directed union of its finitely generated
subgroups, each of them sofic. -/
theorem shiftKernelFor_finset_mem_fg_isSofic {Γ : Type} [Group Γ] [Group.ResiduallyFinite Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex]
    (F : Finset (ShiftKernelFor α hα)) :
    ∃ H : Subgroup (ShiftKernelFor α hα), H.FG ∧ IsSofic H ∧ ∀ g ∈ F, g ∈ H := by
  refine ⟨Subgroup.closure (F : Set (ShiftKernelFor α hα)), ⟨F, rfl⟩, ?_, ?_⟩
  · letI : Group.ResiduallyFinite ↥(Subgroup.closure (F : Set (ShiftKernelFor α hα))) :=
      shiftKernelFor_isLocallyResiduallyFinite α hα
        (Subgroup.closure (F : Set (ShiftKernelFor α hα))) ⟨F, rfl⟩
    exact isSofic_of_isLEF isLEF_of_residuallyFinite
  · intro g hg
    exact Subgroup.subset_closure (Finset.mem_coe.mpr hg)

/-- **Printed sentences** (`non_mf_groups_exist.tex:1566-1568`, proof of
`prop:clifford-locally-rf`).

> The group $W_0$ is their directed union, and $W/W_0\cong\mathbb Z$ is amenable.  Soficity
> passes to directed unions and to extensions with amenable
> quotient~\cite[Theorem~1]{ElekSzabo}, so $W$ is sofic.

Here `W = Ambient α hα` for a residually finite `Γ` with an injective self-embedding `α` of
finite index, and `W₀ = ShiftKernelFor α hα`.  The conjuncts, in printed order:
1. `W₀` is the directed union of its finitely generated subgroups, each of them sofic: every
   finite subset lies in one;
2. `W ≅ W₀ ⋊ ℤ`, and `W₀` is the kernel of the surjection `W₀ ⋊ ℤ → ℤ`;
3. `ℤ` is amenable;
4. soficity passes to directed unions of subgroups;
5. soficity passes to extensions with amenable quotient (Elek--Szabó, Theorem 1);
6. `W` is sofic. -/
def PrintedCliffordWDirectedUnionSofic : Prop :=
  (∀ (Γ : Type) [Group Γ] [Group.ResiduallyFinite Γ] (α : Γ →* Γ)
      (hα : Function.Injective α) [α.range.FiniteIndex] (F : Finset (ShiftKernelFor α hα)),
      ∃ H : Subgroup (ShiftKernelFor α hα), H.FG ∧ IsSofic H ∧ ∀ g ∈ F, g ∈ H) ∧
  (∀ (Γ : Type) [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α),
      Nonempty (Ambient α hα ≃*
        (ShiftKernelFor α hα ⋊[shiftActionFor α hα] Multiplicative ℤ)) ∧
      (SemidirectProduct.inl : ShiftKernelFor α hα →*
          ShiftKernelFor α hα ⋊[shiftActionFor α hα] Multiplicative ℤ).range =
        (SemidirectProduct.rightHom : ShiftKernelFor α hα ⋊[shiftActionFor α hα]
          Multiplicative ℤ →* Multiplicative ℤ).ker ∧
      Function.Surjective (SemidirectProduct.rightHom : ShiftKernelFor α hα ⋊[shiftActionFor α hα]
          Multiplicative ℤ →* Multiplicative ℤ)) ∧
  Amenability.IsAmenable (Multiplicative ℤ) ∧
  (∀ (G : Type) [Group G] (ι : Type) (H : ι → Subgroup G), Directed (· ≤ ·) H →
      (∀ i, IsSofic (H i)) → (∀ g : G, ∃ i, g ∈ H i) → IsSofic G) ∧
  (∀ (G Q : Type) [Group G] [Group Q] (f : G →* Q),
      Function.Surjective f → IsSofic f.ker → Amenability.IsAmenable Q → IsSofic G) ∧
  (∀ (Γ : Type) [Group Γ] [Group.ResiduallyFinite Γ] (α : Γ →* Γ)
      (hα : Function.Injective α) [α.range.FiniteIndex], IsSofic (Ambient α hα))

theorem printedCliffordWDirectedUnionSofic : PrintedCliffordWDirectedUnionSofic := by
  refine ⟨?_, ?_, SoficByAmenablePermanence.isAmenable_int, ?_, ?_, ?_⟩
  · intro Γ _ _ α hα _ F
    exact shiftKernelFor_finset_mem_fg_isSofic α hα F
  · intro Γ _ α hα
    exact ⟨⟨ambientEquivShiftKernelForByInt α hα⟩, SemidirectProduct.range_inl_eq_ker_rightHom,
      SemidirectProduct.rightHom_surjective⟩
  · intro G _ ι H hdir hH hcover
    exact isSofic_of_directedUnion H hdir hH hcover
  · intro G Q _ _ f hf hker hQ
    exact SoficByAmenablePermanence.isSofic_of_isSofic_ker_of_isAmenable f hf hker hQ
  · intro Γ _ _ α hα _
    have hW₀ : IsSofic (ShiftKernelFor α hα) :=
      isSofic_of_every_finset_mem_sofic_subgroup fun F =>
        (shiftKernelFor_finset_mem_fg_isSofic α hα F).imp fun _ hH => hH.2
    exact (isSofic_mulEquiv_iff (ambientEquivShiftKernelForByInt α hα)).mpr
      (SoficByAmenablePermanence.isSofic_int_semidirectProduct (shiftActionFor α hα) hW₀)

/-! ## Related work (tex lines 324--330) -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:327-330`, Related work).

> There, soficity and the rigidity theorems of Kun~\cite{Kun16} and Kun--Thom~\cite{KT19} force
> the centralizing subgroup to be locally embeddable into finite groups, and a copy of
> Thompson's group $V$ gives the contradiction.

"There" is the nonsofic construction [OAI, Proposition 2.3].  The repository packages its
configuration as `CompressionSetup G Γ J`: the finitely generated property-(T) subgroup `Γ`,
the distinguished compressor `u` conjugating `Γ` into itself, and the subgroup `J` centralizing
the compressed copy `u Γ u⁻¹`.  The carrier has three conjuncts, in printed order, each proved
in the repository:
1. soficity forces the centralizing subgroup `J` to be LEF.  This is the rigidity step
   `isLEF_of_isSofic`, in the form proved here from property (T) of the ambient group and of
   `Γ`;
2. Thompson's group `V` is not LEF;
3. so a copy of `V` inside the centralizing subgroup contradicts soficity. -/
def PrintedKunThomRigidityContradiction : Prop :=
  (∀ (G Γ J : Type) [Group G] [Group Γ] [Group J] [Countable G] [Countable Γ] [Countable J]
      (_C : CompressionSetup G Γ J),
      HasKazhdanPropertyT.{0, 0} G → HasKazhdanPropertyT.{0, 0} Γ → IsSofic G → IsLEF J) ∧
  ¬ IsLEF ↥ThompsonV.thompsonV ∧
  (∀ (G Γ J : Type) [Group G] [Group Γ] [Group J] [Countable G] [Countable Γ] [Countable J]
      (_C : CompressionSetup G Γ J),
      HasKazhdanPropertyT.{0, 0} G → HasKazhdanPropertyT.{0, 0} Γ →
      (∃ ι : ↥ThompsonV.thompsonV →* J, Function.Injective ι) → ¬ IsSofic G)

theorem printedKunThomRigidityContradiction : PrintedKunThomRigidityContradiction := by
  refine ⟨?_, BinaryLeavitt.thompsonV_not_isLEF, ?_⟩
  · intro G Γ J _ _ _ _ _ _ C hTG hTΓ hS
    exact isLEF_of_isSofic C hTG hTΓ hS
  · rintro G Γ J _ _ _ _ _ _ C hTG hTΓ ⟨ι, hι⟩ hS
    exact BinaryLeavitt.thompsonV_not_isLEF
      (isLEF_of_injective ι hι (isLEF_of_isSofic C hTG hTΓ hS))

#audit_axioms isSofic_of_directedUnion
#audit_axioms shiftKernelFor_finset_mem_fg_isSofic
#audit_closed_axioms printedIntroWSoficMechanism
#audit_closed_axioms printedCliffordWDirectedUnionSofic
#audit_closed_axioms printedKunThomRigidityContradiction

end SoficCitationSentences
end GroupApproximation
