import GroupApproximation.TypeA2.Statement
import GroupApproximation.TypeA2.Witness
import GroupApproximation.TypeA2.HalfLineWreathEmbedding

/-!
# The image of the witness action is not finitely presented

Let `K` be the kernel of `WitnessGroup ↷ WitnessSet`.  This module shows that `ℤ ≀ ℤ` is a
retract of `WitnessGroup ⧸ K`, so `WitnessGroup ⧸ K` is not finitely presented
(`witness_quotient_not_isFinitelyPresented`).

* Let `g ∈ K`, with free-group part `u`.  Then `γ (replica (witnessPsi u) s) = s` for some
  `γ ∈ geoF 0` and every positive dyadic `s`, so `witnessPsi u = 1`
  (`replica_fixes_of_mul_fixes`, `eq_one_of_replica_fixes`).  Hence `witnessPsi ∘ right`
  descends to `witnessQuotientPsi : WitnessGroup ⧸ K →* compactF 0 1`.
* Its image lies in the injective copy `compactWreath` of `ℤ ≀ ℤ`
  (`wreathEmbedding_injective`).  This gives the retraction `witnessRetraction`.
* If `witnessPsi u = 1`, then `inr u` lies in `K`.  So the classes of the free generators
  satisfy the relations of `ℤ ≀ ℤ`, which gives the section `witnessSection`.
-/

namespace GroupApproximation.TypeA2

open HigmanThompson

/-- `ℤ ≀ ℤ` inside `compactF 0 1`. -/
noncomputable def compactWreath : IntWreath →* compactF 0 1 :=
  witnessEquiv.toMonoidHom.comp wreathEmbedding

theorem compactWreath_injective : Function.Injective compactWreath :=
  witnessEquiv.injective.comp wreathEmbedding_injective

theorem compactWreath_lamp : compactWreath IntWreath.lamp = witnessEquiv lampF :=
  congrArg witnessEquiv wreathEmbedding_lamp

theorem compactWreath_shift : compactWreath IntWreath.shift = witnessEquiv shiftF :=
  congrArg witnessEquiv wreathEmbedding_shift

theorem witnessPsi_mem_range (u : FreeGroup (Fin 2)) : witnessPsi u ∈ compactWreath.range := by
  have hle : witnessPsi.range ≤ compactWreath.range := by
    refine FreeGroup.range_lift_le ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact MonoidHom.mem_range.mpr ⟨IntWreath.lamp, compactWreath_lamp⟩
    · exact MonoidHom.mem_range.mpr ⟨IntWreath.shift, compactWreath_shift⟩
  exact hle (MonoidHom.mem_range.mpr ⟨u, rfl⟩)

/-- An element acting trivially has trivial free-group part modulo `ker witnessPsi`. -/
theorem witnessPsi_right_eq_one {g : WitnessGroup}
    (hg : g ∈ actionKernel WitnessGroup WitnessSet) : witnessPsi g.right = 1 := by
  have hfix : ∀ s ∈ posGrid 0,
      (g.left : Equiv.Perm ℚ) (replica (witnessPsi g.right).2 s) = s := fun s hs =>
    congrArg Subtype.val (mem_actionKernel.mp hg ⟨s, hs⟩)
  exact Subtype.ext (eq_one_of_replica_fixes (witnessPsi g.right).2
    (replica_fixes_of_mul_fixes (witnessPsi g.right).2 g.left.2 hfix))

theorem witnessKernel_le :
    actionKernel WitnessGroup WitnessSet ≤ (witnessPsi.comp SemidirectProduct.rightHom).ker :=
  fun _ hg => MonoidHom.mem_ker.mpr (witnessPsi_right_eq_one hg)

/-- `witnessPsi ∘ right`, descended to the image of the witness action. -/
noncomputable def witnessQuotientPsi :
    WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet →* compactF 0 1 :=
  QuotientGroup.lift (actionKernel WitnessGroup WitnessSet)
    (witnessPsi.comp SemidirectProduct.rightHom) witnessKernel_le

theorem witnessQuotientPsi_mem_range (q : WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet) :
    witnessQuotientPsi q ∈ compactWreath.range := by
  induction q using QuotientGroup.induction_on with
  | H g => exact witnessPsi_mem_range g.right

/-- The retraction `WitnessGroup ⧸ K →* ℤ ≀ ℤ`. -/
noncomputable def witnessRetraction :
    WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet →* IntWreath :=
  (MonoidHom.ofInjective compactWreath_injective).symm.toMonoidHom.comp
    (witnessQuotientPsi.codRestrict compactWreath.range witnessQuotientPsi_mem_range)

/-- The free group, mapped into the image of the witness action. -/
noncomputable def witnessSection0 :
    FreeGroup (Fin 2) →* WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet :=
  (QuotientGroup.mk' (actionKernel WitnessGroup WitnessSet)).comp SemidirectProduct.inr

theorem witness_inr_mem_actionKernel {w : FreeGroup (Fin 2)} (hw : witnessPsi w = 1) :
    (SemidirectProduct.inr w : WitnessGroup) ∈ actionKernel WitnessGroup WitnessSet := by
  have h1 : witnessPhi w = 1 := by
    rw [witnessPhi, MonoidHom.comp_apply, hw, map_one]
  refine mem_actionKernel.mpr fun s => Subtype.ext ?_
  show ((1 : geoF 0) : Equiv.Perm ℚ) (witnessPhi w s) = s
  simp only [h1, Subgroup.coe_one, Equiv.Perm.one_apply]

theorem witnessSection0_eq {u v : FreeGroup (Fin 2)} (h : witnessPsi u = witnessPsi v) :
    witnessSection0 u = witnessSection0 v := by
  show ((SemidirectProduct.inr u : WitnessGroup) :
      WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet) = (SemidirectProduct.inr v : WitnessGroup)
  rw [QuotientGroup.eq, ← map_inv, ← map_mul]
  exact witness_inr_mem_actionKernel (by rw [map_mul, map_inv, h, inv_mul_cancel])

theorem witnessSection0_commute {x y : FreeGroup (Fin 2)}
    (h : Commute (witnessPsi x) (witnessPsi y)) :
    Commute (witnessSection0 x) (witnessSection0 y) := by
  show witnessSection0 x * witnessSection0 y = witnessSection0 y * witnessSection0 x
  rw [← map_mul, ← map_mul]
  exact witnessSection0_eq (by rw [map_mul, map_mul]; exact h.eq)

theorem witnessSection0_conj_commute (i j : ℤ) :
    Commute (witnessSection0 (FreeGroup.of 1) ^ i * witnessSection0 (FreeGroup.of 0) *
        (witnessSection0 (FreeGroup.of 1) ^ i)⁻¹)
      (witnessSection0 (FreeGroup.of 1) ^ j * witnessSection0 (FreeGroup.of 0) *
        (witnessSection0 (FreeGroup.of 1) ^ j)⁻¹) := by
  have key : ∀ k : ℤ, witnessSection0 (FreeGroup.of 1) ^ k * witnessSection0 (FreeGroup.of 0) *
      (witnessSection0 (FreeGroup.of 1) ^ k)⁻¹ =
      witnessSection0 (FreeGroup.of 1 ^ k * FreeGroup.of 0 * (FreeGroup.of 1 ^ k)⁻¹) :=
    fun k => by simp only [map_mul, map_inv, map_zpow]
  have hpsi : ∀ k : ℤ,
      witnessPsi (FreeGroup.of 1 ^ k * FreeGroup.of 0 * (FreeGroup.of 1 ^ k)⁻¹) =
        witnessEquiv (shiftF ^ k * lampF * (shiftF ^ k)⁻¹) :=
    fun k => by simp only [map_mul, map_inv, map_zpow, witnessPsi_of_zero, witnessPsi_of_one]
  rw [key i, key j]
  apply witnessSection0_commute
  rw [hpsi i, hpsi j]
  exact (shiftF_conj_commute i j).map witnessEquiv

/-- The section `ℤ ≀ ℤ →* WitnessGroup ⧸ K`, sending lamp and shift to the free generators. -/
noncomputable def witnessSection :
    IntWreath →* WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet :=
  IntWreath.lift (witnessSection0 (FreeGroup.of 0)) (witnessSection0 (FreeGroup.of 1))
    witnessSection0_conj_commute

theorem witnessRetraction_section_lamp :
    witnessRetraction (witnessSection IntWreath.lamp) = IntWreath.lamp := by
  rw [witnessRetraction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [MonoidHom.ofInjective_apply, compactWreath_lamp]
  show witnessQuotientPsi (witnessSection IntWreath.lamp) = _
  rw [witnessSection, IntWreath.lift_lamp]
  exact witnessPsi_of_zero

theorem witnessRetraction_section_shift :
    witnessRetraction (witnessSection IntWreath.shift) = IntWreath.shift := by
  rw [witnessRetraction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [MonoidHom.ofInjective_apply, compactWreath_shift]
  show witnessQuotientPsi (witnessSection IntWreath.shift) = _
  rw [witnessSection, IntWreath.lift_shift]
  exact witnessPsi_of_one

theorem witnessRetraction_section (q : IntWreath) : witnessRetraction (witnessSection q) = q := by
  have h : witnessRetraction.comp witnessSection = MonoidHom.id IntWreath :=
    IntWreath.hom_ext witnessRetraction_section_lamp witnessRetraction_section_shift
  exact DFunLike.congr_fun h q

/-- **The image of the witness action is not finitely presented**: it retracts onto
`ℤ ≀ ℤ`. -/
theorem witness_quotient_not_isFinitelyPresented :
    ¬ Group.IsFinitelyPresented (WitnessGroup ⧸ actionKernel WitnessGroup WitnessSet) :=
  not_isFinitelyPresented_of_retract witnessSection witnessRetraction witnessRetraction_section
    IntWreath.not_isFinitelyPresented

end GroupApproximation.TypeA2
