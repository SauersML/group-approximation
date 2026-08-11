import NonsoficGroupsExist.Kazhdan.KazhdanComplex
import NonsoficGroupsExist.PropertyT.FreeElementaryPropertyT

/-!
# Localized complex displacement for a free elementary plane

The Fourier estimate for `E₃` is real.  This file realifies a complex
representation after an arbitrary group homomorphism and exposes exactly the
six root bounds used by that estimate.  No bounds on the other elementary
root directions are required.
-/

namespace NonsoficGroupsExist

open scoped InnerProductSpace
open FreeElementaryPropertyT
open FreeRootCharacterValuation

universe u v

variable (X : Type*) [Fintype X]
variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Local control in four root directions bounds displacement by every
element of their common-terminal-index plane, after composition with any
group homomorphism. -/
theorem norm_comp_columnPlane_sub_le_of_root_bounds
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (f : elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X) →* G)
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (z : E) {B : ℝ} (hB : 0 ≤ B)
    (hIK : ‖rho (f (elementaryRoot i k hik 1)) z - z‖ ≤ B)
    (hJK : ‖rho (f (elementaryRoot j k hjk 1)) z - z‖ ≤ B)
    (hIJUnit : ‖rho (f (elementaryRoot i j hij 1)) z - z‖ ≤ B)
    (hJIUnit : ‖rho (f (elementaryRoot j i hij.symm 1)) z - z‖ ≤ B)
    (hIJGen : ∀ q : Fin (Fintype.card X),
      ‖rho (f (elementaryRoot i j hij
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)))) z - z‖ ≤ B)
    (hJIGen : ∀ q : Fin (Fintype.card X),
      ‖rho (f (elementaryRoot j i hij.symm
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)))) z - z‖ ≤ B)
    (g : elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X))
    (hg : g ∈ elementaryRootSubgroup i k hik ⊔
      elementaryRootSubgroup j k hjk) :
    ‖rho (f g) z - z‖ ≤
      2 * (6 * Fintype.card X + 6 : ℝ) * (B + 1) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let rhoR : elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X) →*
      (E ≃ₗᵢ[ℝ] E) := realifyHom (rho.comp f)
  have hdelta : 0 < B + 1 := by linarith
  have hmoving := norm_columnPlaneMovingProjection_le_of_root_bounds X
    i j k hij hik hjk rhoR z hdelta
    (lt_of_le_of_lt hIK (lt_add_one B))
    (lt_of_le_of_lt hJK (lt_add_one B))
    (lt_of_le_of_lt hIJUnit (lt_add_one B))
    (lt_of_le_of_lt hJIUnit (lt_add_one B))
    (fun q ↦ lt_of_le_of_lt (hIJGen q) (lt_add_one B))
    (fun q ↦ lt_of_le_of_lt (hJIGen q) (lt_add_one B))
  have hdisp :=
    KazhdanFixedSpace.norm_displacement_le_two_mul_norm_subgroupMovingProjection_of_mem
      rhoR (elementaryRootSubgroup i k hik ⊔
        elementaryRootSubgroup j k hjk) hg z
  change ‖rho (f g) z - z‖ ≤ _
  calc
    ‖rho (f g) z - z‖ ≤
        2 * ‖KazhdanFixedSpace.subgroupMovingProjection rhoR
          (elementaryRootSubgroup i k hik ⊔
            elementaryRootSubgroup j k hjk) z‖ := hdisp
    _ ≤ 2 * ((6 * Fintype.card X + 6 : ℝ) * (B + 1)) :=
      mul_le_mul_of_nonneg_left hmoving (by norm_num)
    _ = 2 * (6 * Fintype.card X + 6 : ℝ) * (B + 1) := by ring

end NonsoficGroupsExist
