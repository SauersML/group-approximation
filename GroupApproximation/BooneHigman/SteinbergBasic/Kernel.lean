import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Algebra.FinitePresentationKernel

/-!
# The unstable `K₂` kernel of a Steinberg group

For a finite index type `I` and a unital ring `R`, `SteinbergGroup I R` is the group presented by the
generators `xᵢⱼ(a)` (`i ≠ j`, `a ∈ R`) and the three Steinberg relations, and
`SteinbergGroup.projection` is the canonical surjection onto the elementary group `elementaryGroup I R`
(`GroupApproximation/Steinberg/Basic.lean`).

This file names the kernel of that projection,

  `K2 I R = ker (St_I(R) → E_I(R))`,

the unstable `K₂(I, R)`, and records the finite-presentation transfer between the two groups.  When
`St_I(R)` is finitely presented, `E_I(R)` is finitely presented exactly when `K2 I R` is the normal closure
of a finite set.  This is the form in which the finite presentation of the affine hosts `P^N ⋊ E_N(P)`
consumes `K₂` information.

The `ℕ`-indexed forms `St n R` and `K2n n R` use the index type `Fin n`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace SteinbergBasic

open SteinbergGroup

section General

variable (I R : Type*) [Fintype I] [DecidableEq I] [Ring R]

/-- The unstable `K₂(I, R)`: the kernel of the canonical projection `St_I(R) → E_I(R)`. -/
def K2 : Subgroup (SteinbergGroup I R) :=
  (projection (I := I) (R := R)).ker

instance K2_normal : (K2 I R).Normal :=
  MonoidHom.normal_ker _

variable {I R}

theorem mem_K2_iff (g : SteinbergGroup I R) :
    g ∈ K2 I R ↔ projection g = 1 :=
  MonoidHom.mem_ker

theorem K2_eq_bot_iff :
    K2 I R = ⊥ ↔ Function.Injective (projection (I := I) (R := R)) :=
  MonoidHom.ker_eq_bot_iff _

/-- `St_I(R) ⧸ K₂(I,R) ≃* E_I(R)`. -/
noncomputable def quotientK2Equiv :
    SteinbergGroup I R ⧸ K2 I R ≃* elementaryGroup I R :=
  QuotientGroup.quotientKerEquivOfSurjective (projection (I := I) (R := R)) projection_surjective

/-- When `K₂(I,R)` is trivial, the canonical projection is an isomorphism `St_I(R) ≃* E_I(R)`. -/
noncomputable def equivOfK2EqBot (h : K2 I R = ⊥) :
    SteinbergGroup I R ≃* elementaryGroup I R :=
  MulEquiv.ofBijective (projection (I := I) (R := R))
    ⟨K2_eq_bot_iff.mp h, projection_surjective⟩

@[simp] theorem equivOfK2EqBot_apply (h : K2 I R = ⊥) (g : SteinbergGroup I R) :
    equivOfK2EqBot h g = projection g := rfl

/-- If `St_I(R)` is finitely presented and `K₂(I,R)` is finitely normally generated, then `E_I(R)` is
finitely presented. -/
theorem isFinitelyPresented_elementaryGroup_of
    [Group.IsFinitelyPresented (SteinbergGroup I R)]
    (hK : (K2 I R).IsFinitelyNormallyGenerated) :
    Group.IsFinitelyPresented (elementaryGroup I R) :=
  Group.IsFinitelyPresented.of_surjective (projection (I := I) (R := R)) projection_surjective hK

/-- If `St_I(R)` is finitely presented and `K₂(I,R)` is trivial, then `E_I(R)` is finitely presented. -/
theorem isFinitelyPresented_elementaryGroup_of_K2_eq_bot
    [Group.IsFinitelyPresented (SteinbergGroup I R)] (h : K2 I R = ⊥) :
    Group.IsFinitelyPresented (elementaryGroup I R) := by
  apply isFinitelyPresented_elementaryGroup_of
  rw [h]
  exact Subgroup.IsFinitelyNormallyGenerated.bot

/-- The Tietze converse: if both `St_I(R)` and `E_I(R)` are finitely presented, then `K₂(I,R)` is finitely
normally generated. -/
theorem K2_isFinitelyNormallyGenerated_of
    [Group.IsFinitelyPresented (SteinbergGroup I R)]
    [Group.IsFinitelyPresented (elementaryGroup I R)] :
    (K2 I R).IsFinitelyNormallyGenerated :=
  Tietze.ker_isFinitelyNormallyGenerated (projection (I := I) (R := R)) projection_surjective

theorem isFinitelyPresented_elementaryGroup_iff
    [Group.IsFinitelyPresented (SteinbergGroup I R)] :
    Group.IsFinitelyPresented (elementaryGroup I R) ↔ (K2 I R).IsFinitelyNormallyGenerated :=
  ⟨fun _ ↦ K2_isFinitelyNormallyGenerated_of, isFinitelyPresented_elementaryGroup_of⟩

end General

section Nat

/-- `St_n(R)`, the Steinberg group on the index type `Fin n`. -/
abbrev St (n : ℕ) (R : Type*) [Ring R] : Type _ :=
  SteinbergGroup (Fin n) R

/-- `K₂(n, R)`, the unstable `K₂` on the index type `Fin n`. -/
abbrev K2n (n : ℕ) (R : Type*) [Ring R] : Subgroup (St n R) :=
  K2 (Fin n) R

end Nat

end SteinbergBasic
end BooneHigman
end GroupApproximation
