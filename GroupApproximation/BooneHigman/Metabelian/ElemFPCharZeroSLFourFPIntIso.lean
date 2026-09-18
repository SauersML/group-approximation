import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPComm
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPIntPres
import GroupApproximation.Meta.AxiomGuard

/-!
# `St_I(ℤ)` is finitely presented (bh-met-91f)

The inverse of `czSLFourFP_phi` sends `xᵢⱼ(a)` to `yᵢⱼ ^ a`.  The three Steinberg relator
families hold for these images:

* additivity is `zpow_add`;
* commutation follows from `⁅yᵢⱼ, yₖₗ⁆ = 1` by `Commute.zpow_zpow`;
* the adjacent relation `⁅yᵢⱼ ^ a, yⱼₖ ^ b⁆ = yᵢₖ ^ (a * b)` is
  `czSLFourFP_commutator_zpow_zpow`, because `yᵢₖ` commutes with `yᵢⱼ` and `yⱼₖ`.

Both composites are the identity on generators (`xᵢⱼ(1) ^ a = xᵢⱼ(a)`), so
`czSLFourFP_intEquiv : czSLFourFP_IntGroup I ≃* St_I(ℤ)` and `St_I(ℤ)` is finitely presented for
every finite index type `I` (`czSLFourFP_stInt_isFinitelyPresented`).  No rank
hypothesis and no literature input is used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

noncomputable section

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- `xᵢⱼ(1) ^ a = xᵢⱼ(a)` in `St_I(ℤ)`. -/
theorem czSLFourFP_x_one_zpow (i j : I) (hij : i ≠ j) (a : ℤ) :
    SteinbergGroup.x i j hij (1 : ℤ) ^ a = SteinbergGroup.x i j hij a := by
  induction a with
  | zero => rw [zpow_zero, SteinbergGroup.x_zero]
  | succ n ih => rw [zpow_add_one, ih, SteinbergGroup.x_mul]
  | pred n ih =>
      rw [zpow_sub_one, ih, ← SteinbergGroup.x_neg, SteinbergGroup.x_mul, sub_eq_add_neg]

/-- Images `yᵢⱼ ^ a` of the Steinberg generators. -/
def czSLFourFP_psiGen (g : SteinbergGenerator I ℤ) : czSLFourFP_IntGroup I :=
  czSLFourFP_y I g.row g.column g.row_ne_column ^ g.coefficient

theorem czSLFourFP_psi_rels : ∀ r ∈ SteinbergGroup.relations (I := I) (R := ℤ),
    FreeGroup.lift (czSLFourFP_psiGen I) r = 1 := by
  intro r hr
  change SteinbergGroup.IsRelation r at hr
  cases hr with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change czSLFourFP_y I i j hij ^ a * czSLFourFP_y I i j hij ^ b *
        (czSLFourFP_y I i j hij ^ (a + b))⁻¹ = 1
      rw [← zpow_add, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      exact ((czSLFourFP_y_commute I i j k l hij hkl hjk hli).zpow_zpow a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (czSLFourFP_commutator_zpow_zpow
        (czSLFourFP_y_commutator I i j k hij hjk hik)
        (czSLFourFP_y_commute I i j i k hij hik hij.symm hik.symm)
        (czSLFourFP_y_commute I j k i k hjk hik hik.symm hjk.symm) a b)

/-- The homomorphism `ψ : xᵢⱼ(a) ↦ yᵢⱼ ^ a`. -/
def czSLFourFP_psi : SteinbergGroup I ℤ →* czSLFourFP_IntGroup I :=
  PresentedGroup.toGroup (czSLFourFP_psi_rels I)

theorem czSLFourFP_psi_x (i j : I) (hij : i ≠ j) (a : ℤ) :
    czSLFourFP_psi I (SteinbergGroup.x i j hij a) = czSLFourFP_y I i j hij ^ a :=
  PresentedGroup.toGroup.of (czSLFourFP_psi_rels I)

theorem czSLFourFP_psi_comp_phi :
    (czSLFourFP_psi I).comp (czSLFourFP_phi I) = MonoidHom.id (czSLFourFP_IntGroup I) := by
  apply PresentedGroup.ext
  rintro ⟨⟨i, j⟩, hij⟩
  change czSLFourFP_psi I (czSLFourFP_phi I (czSLFourFP_y I i j hij)) = czSLFourFP_y I i j hij
  rw [czSLFourFP_phi_y, czSLFourFP_psi_x, zpow_one]

theorem czSLFourFP_phi_comp_psi :
    (czSLFourFP_phi I).comp (czSLFourFP_psi I) = MonoidHom.id (SteinbergGroup I ℤ) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change czSLFourFP_phi I (czSLFourFP_psi I (SteinbergGroup.x i j hij a)) =
    SteinbergGroup.x i j hij a
  rw [czSLFourFP_psi_x, map_zpow, czSLFourFP_phi_y, czSLFourFP_x_one_zpow]

/-- `czSLFourFP_IntGroup I ≃* St_I(ℤ)`. -/
def czSLFourFP_intEquiv : czSLFourFP_IntGroup I ≃* SteinbergGroup I ℤ :=
  MonoidHom.toMulEquiv (czSLFourFP_phi I) (czSLFourFP_psi I) (czSLFourFP_psi_comp_phi I)
    (czSLFourFP_phi_comp_psi I)

/-- **`St_I(ℤ)` is finitely presented** for every finite index type `I`. -/
theorem czSLFourFP_stInt_isFinitelyPresented :
    Group.IsFinitelyPresented (SteinbergGroup I ℤ) :=
  haveI := czSLFourFP_intGroup_isFinitelyPresented I
  Group.IsFinitelyPresented.equiv (czSLFourFP_intEquiv I)

end

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_x_one_zpow
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_psiGen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_psi_rels
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_psi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_psi_x
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_psi_comp_phi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_phi_comp_psi
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_intEquiv
#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_stInt_isFinitelyPresented

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
