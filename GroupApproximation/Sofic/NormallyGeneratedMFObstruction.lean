import GroupApproximation.Sofic.NormMFResidualFunctorial
import Mathlib.GroupTheory.IsPerfect

/-!
# Normally generated MF obstructions

An MF-invisible element which normally generates its ambient group forces the
whole norm-MF residual to be the ambient group.  Consequently every
homomorphism to a group with trivial norm-MF residual is trivial.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

variable {Γ : Type u} [Group Γ]

/-- A homomorphism is trivial as soon as it kills an element which normally
generates its source.  This is the purely algebraic bridge from a marked
finite-dimensional kill theorem to field-general representation-triviality
of a normally generated envelope; it makes no assumption on the target. -/
theorem hom_eq_one_of_map_eq_one_of_normalClosure_eq_top {x : Γ}
    (hgen : Subgroup.normalClosure ({x} : Set Γ) = ⊤)
    {M : Type v} [Group M] (f : Γ →* M) (hx : f x = 1) : f = 1 := by
  apply MonoidHom.ext
  intro g
  have hclosure : Subgroup.normalClosure ({x} : Set Γ) ≤ f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (MonoidHom.mem_ker).mpr hx
  apply MonoidHom.mem_ker.mp
  apply hclosure
  rw [hgen]
  exact Subgroup.mem_top g

/-- If a normally generating element lies in the commutator subgroup, then
the whole group is perfect. -/
theorem isPerfect_of_mem_commutator_normalClosure_eq_top {x : Γ}
    (hx : x ∈ commutator Γ)
    (hgen : Subgroup.normalClosure ({x} : Set Γ) = ⊤) :
    Group.IsPerfect Γ := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro g _
  have hclosure : Subgroup.normalClosure ({x} : Set Γ) ≤ commutator Γ := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hx
  apply hclosure
  rw [hgen]
  exact Subgroup.mem_top g

/-- If an MF-invisible element normally generates the group, then every
element is MF-invisible. -/
theorem normMFResidual_eq_top_of_mem_normalClosure_eq_top {x : Γ}
    (hx : x ∈ normMFResidual Γ)
    (hgen : Subgroup.normalClosure ({x} : Set Γ) = ⊤) :
    normMFResidual Γ = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  simpa [hy] using hx

/-- Full source residual and trivial target residual force every homomorphism
to be pointwise trivial.  No countability hypothesis is needed. -/
theorem map_eq_one_of_residual_eq_top_to_residual_eq_bot
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] (hM : normMFResidual M = ⊥)
    (f : Γ →* M) (g : Γ) : f g = 1 := by
  have hg : g ∈ normMFResidual Γ := by
    rw [hΓ]
    exact Subgroup.mem_top g
  have hfg : f g ∈ normMFResidual M :=
    mem_normMFResidual_iff.mpr
      ((mem_normMFResidual_iff.mp hg).map f)
  rw [hM] at hfg
  exact Subgroup.mem_bot.mp hfg

/-- Homomorphism-level form of
`map_eq_one_of_residual_eq_top_to_residual_eq_bot`. -/
theorem hom_eq_one_of_residual_eq_top_to_residual_eq_bot
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] (hM : normMFResidual M = ⊥)
    (f : Γ →* M) : f = 1 := by
  ext g
  exact map_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ hM f g

/-- A full-residual group has no nontrivial quotient whose residual is
trivial. -/
theorem not_surjective_of_residual_eq_top_to_residual_eq_bot
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Nontrivial M]
    (hM : normMFResidual M = ⊥) (f : Γ →* M) :
    ¬ Function.Surjective f := by
  intro hsurj
  obtain ⟨m, hm⟩ := exists_ne (1 : M)
  obtain ⟨g, rfl⟩ := hsurj m
  exact hm (map_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ hM f g)

/-- Every homomorphism from a full-residual group to a countable
operator-MF group is trivial. -/
theorem hom_eq_one_of_residual_eq_top_to_isOperatorMF
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M]
    (hM : IsOperatorMF M) (f : Γ →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isOperatorMF hM) f

/-- There is no nontrivial countable operator-MF quotient of a
full-residual group. -/
theorem not_surjective_of_residual_eq_top_to_isOperatorMF
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M] [Nontrivial M]
    (hM : IsOperatorMF M) (f : Γ →* M) :
    ¬ Function.Surjective f :=
  not_surjective_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isOperatorMF hM) f

/-- Every homomorphism from a full-residual group to a finite group is
trivial. -/
theorem hom_eq_one_of_residual_eq_top_to_finite
    (hΓ : normMFResidual Γ = ⊤)
    (M : Type) [Group M] [Finite M] (f : Γ →* M) : f = 1 := by
  exact hom_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF (isWeakMF_of_finite M)) f

/-- A full-residual group has no nontrivial finite quotient. -/
theorem not_surjective_of_residual_eq_top_to_finite
    (hΓ : normMFResidual Γ = ⊤)
    (M : Type) [Group M] [Finite M] [Nontrivial M]
    (f : Γ →* M) : ¬ Function.Surjective f := by
  exact not_surjective_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF (isWeakMF_of_finite M)) f

/-- Every homomorphism from a full-residual group to a countable residually
finite group is trivial. -/
theorem hom_eq_one_of_residual_eq_top_to_residuallyFinite
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M] [Group.ResiduallyFinite M]
    (f : Γ →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF
      (isWeakMF_of_residuallyFinite (H := M))) f

/-- A full-residual group has no nontrivial countable residually finite
quotient. -/
theorem not_surjective_of_residual_eq_top_to_residuallyFinite
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M] [Group.ResiduallyFinite M]
    [Nontrivial M] (f : Γ →* M) : ¬ Function.Surjective f :=
  not_surjective_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF
      (isWeakMF_of_residuallyFinite (H := M))) f

end GroupApproximation
