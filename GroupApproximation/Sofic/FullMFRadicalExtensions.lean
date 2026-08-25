import GroupApproximation.Sofic.FullMFRadicalProducts

/-!
# Extension laws for the intrinsic MF core

The intrinsically full class and the core-free class are both stable under
extensions.  The core-free statement has a stronger map form: if the target
of a homomorphism and its kernel are core-free, then the source is core-free;
surjectivity is not required.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-- A surjection with full-core kernel and full-core target has full-core
source. -/
theorem fullMFRadicalCore_eq_top_of_surjective_kernel
    {H : Type v} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (hker : fullMFRadicalCore f.ker = ⊤)
    (hH : fullMFRadicalCore H = ⊤) :
    fullMFRadicalCore G = ⊤ := by
  apply (fullMFRadicalCore_eq_top_iff (G := G)).mpr
  exact actualCoronaMFResidual_eq_top_of_surjective_kernel f hf
    ((fullMFRadicalCore_eq_top_iff (G := f.ker)).mp hker)
    ((fullMFRadicalCore_eq_top_iff (G := H)).mp hH)

/-- If the target of a homomorphism and its kernel are core-free, then its
source is core-free. -/
theorem fullMFRadicalCore_eq_bot_of_target_eq_bot_of_ker_eq_bot
    {H : Type v} [Group H] (f : G →* H)
    (hH : fullMFRadicalCore H = ⊥)
    (hker : fullMFRadicalCore f.ker = ⊥) :
    fullMFRadicalCore G = ⊥ := by
  have hCker : fullMFRadicalCore G ≤ f.ker :=
    fullMFRadicalCore_le_ker_of_target_eq_bot f hH
  let j : fullMFRadicalCore G →* f.ker :=
    Subgroup.inclusion hCker
  have hj : j = 1 :=
    hom_eq_one_of_source_core_eq_top_of_target_core_eq_bot j
      fullMFRadicalCore_idempotent hker
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  let y : fullMFRadicalCore G := ⟨x, hx⟩
  have hy : j y = 1 := DFunLike.congr_fun hj y
  exact congrArg Subtype.val hy

/-- An extension of a core-free group by a core-free group is core-free. -/
theorem fullMFRadicalCore_eq_bot_of_normal_and_quotient_eq_bot
    (N : Subgroup G) [N.Normal]
    (hN : fullMFRadicalCore N = ⊥)
    (hQ : fullMFRadicalCore (G ⧸ N) = ⊥) :
    fullMFRadicalCore G = ⊥ := by
  apply fullMFRadicalCore_eq_bot_of_target_eq_bot_of_ker_eq_bot
    (QuotientGroup.mk' N) hQ
  rw [QuotientGroup.ker_mk']
  exact hN

end GroupApproximation
