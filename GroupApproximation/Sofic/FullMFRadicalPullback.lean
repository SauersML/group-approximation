import GroupApproximation.Sofic.FullMFRadicalLocalization

/-!
# Pullback formulas for the intrinsic MF core

Across a surjection with intrinsically full kernel, the source core is exactly
the inverse image of the target core.  More generally, a homomorphism with
full-core kernel and core-free target has core equal to its kernel, without a
surjectivity hypothesis.  The same kernel formula holds for the genuine
norm-matrix-corona residual when the target residual is trivial.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- A full-kernel surjection computes the source core as the inverse image of
the target core. -/
theorem fullMFRadicalCore_eq_comap_of_surjective_of_kernel_eq_top
    (f : G →* H) (hf : Function.Surjective f)
    (hker : actualCoronaMFResidual f.ker = ⊤) :
    fullMFRadicalCore G = (fullMFRadicalCore H).comap f := by
  apply le_antisymm
  · intro x hx
    exact map_fullMFRadicalCore_le f
      (Subgroup.mem_map_of_mem f hx)
  · intro x hx
    change f x ∈ fullMFRadicalCore H at hx
    have hmap :=
      map_fullMFRadicalCore_eq_of_surjective_of_kernel_eq_top f hf hker
    rw [← hmap] at hx
    obtain ⟨c, hc, hfc⟩ := hx
    have hk : x * c⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfc]
      simp
    have hkerCore : f.ker ≤ fullMFRadicalCore G :=
      le_fullMFRadicalCore f.ker hker
    have hprod :=
      (fullMFRadicalCore G).mul_mem (hkerCore hk) hc
    simpa [mul_assoc] using hprod

/-- If a homomorphism has full-core kernel and core-free target, then the
source core is exactly its kernel.  Surjectivity is unnecessary. -/
theorem fullMFRadicalCore_eq_ker_of_kernel_eq_top_of_target_eq_bot
    (f : G →* H)
    (hker : fullMFRadicalCore f.ker = ⊤)
    (hH : fullMFRadicalCore H = ⊥) :
    fullMFRadicalCore G = f.ker := by
  apply le_antisymm
  · exact fullMFRadicalCore_le_ker_of_target_eq_bot f hH
  · exact le_fullMFRadicalCore f.ker
      ((fullMFRadicalCore_eq_top_iff (G := f.ker)).mp hker)

/-- If a homomorphism has intrinsically full kernel and target with trivial
genuine-corona residual, then that kernel is the exact source residual. -/
theorem actualCoronaMFResidual_eq_ker_of_kernel_eq_top_of_target_eq_bot
    (f : G →* H)
    (hker : actualCoronaMFResidual f.ker = ⊤)
    (hH : actualCoronaMFResidual H = ⊥) :
    actualCoronaMFResidual G = f.ker := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hmap : f x ∈ (actualCoronaMFResidual G).map f :=
      Subgroup.mem_map_of_mem f hx
    have hin : f x ∈ actualCoronaMFResidual H :=
      map_actualCoronaMFResidual_le f hmap
    rw [hH] at hin
    exact Subgroup.mem_bot.mp hin
  · intro x hx
    have hx' : (⟨x, hx⟩ : f.ker) ∈ actualCoronaMFResidual f.ker := by
      rw [hker]
      exact Subgroup.mem_top _
    exact map_actualCoronaMFResidual_le f.ker.subtype
      (Subgroup.mem_map_of_mem f.ker.subtype hx')

end GroupApproximation
