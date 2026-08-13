import GroupApproximation.Sofic.KazhdanCompressionCore

/-!
# Functoriality of Kazhdan-compression defects

Kazhdan-compression data passes through an arbitrary group homomorphism.
Moreover, the image of the source defect normal closure is contained in the
defect normal closure of the mapped core.  This is the algebraic transport
needed when a corona representation is replaced by its range.
-/

namespace GroupApproximation
namespace KazhdanCompressionCore

open scoped commutatorElement

universe u v

variable {Γ : Type} {E : Type u} {H : Type v}
  [Group Γ] [Group E] [Group H]

/-- Transport a Kazhdan-compression core along a group homomorphism. -/
def map (C : KazhdanCompressionCore Γ E) (f : E →* H) :
    KazhdanCompressionCore Γ H where
  iota := f.comp C.iota
  t := f C.t
  c := f C.c
  kazhdan := C.kazhdan
  compresses γ := by
    obtain ⟨δ, hδ⟩ := C.compresses γ
    refine ⟨δ, ?_⟩
    simpa only [map_mul, map_inv, MonoidHom.coe_comp, Function.comp_apply]
      using congrArg f hδ
  comm_c γ := (C.comm_c γ).map f

@[simp]
theorem map_iota (C : KazhdanCompressionCore Γ E) (f : E →* H) (γ : Γ) :
    (C.map f).iota γ = f (C.iota γ) :=
  rfl

@[simp]
theorem map_transported (C : KazhdanCompressionCore Γ E) (f : E →* H) :
    (C.map f).transported = f C.transported := by
  simp [transported, map]

@[simp]
theorem map_defect (C : KazhdanCompressionCore Γ E) (f : E →* H) (γ : Γ) :
    ⁅(C.map f).transported, (C.map f).iota γ⁆ =
      f ⁅C.transported, C.iota γ⁆ := by
  simp

/-- Every element of the original defect normal closure maps into the defect
normal closure of the transported core. -/
theorem defectNormal_le_comap_map_defectNormal
    (C : KazhdanCompressionCore Γ E) (f : E →* H) :
    C.defectNormal ≤ (C.map f).defectNormal.comap f := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨γ, rfl⟩
  change f ⁅C.transported, C.iota γ⁆ ∈ (C.map f).defectNormal
  rw [← C.map_defect f γ]
  exact (C.map f).defect_mem_defectNormal γ

/-- Containment in the compression defect survives passage to a homomorphic
image. -/
theorem map_subgroup_le_defectNormal
    (C : KazhdanCompressionCore Γ E) (f : E →* H)
    (K : Subgroup E) (hK : K ≤ C.defectNormal) :
    K.map f ≤ (C.map f).defectNormal := by
  rintro y ⟨x, hx, rfl⟩
  exact C.defectNormal_le_comap_map_defectNormal f (hK hx)

end KazhdanCompressionCore
end GroupApproximation
