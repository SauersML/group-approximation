import GroupApproximation.Kazhdan.Kazhdan
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Marker-free Kazhdan-compression data

This module records exactly the group-theoretic input used by the compressor
and finite-normal obstruction: a property-`(T)` source mapped into an ambient
group, a one-sided compressor of its image, and a root centralizing that
image.  It deliberately contains no marked element, torsion relation, or
central marked word.

The compression-defect subgroup is the normal closure of the pointwise
commutators `[t c t⁻¹, ι(γ)]`.  Its elementary normal-closure API is kept here
so the analytic files depend on a genuinely marker-free interface.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

/-- The exact marker-free input to Kazhdan compression. -/
structure KazhdanCompressionCore (Γ : Type v) (E : Type u) [Group Γ]
    [Group E] where
  /-- The Kazhdan source mapped into the ambient group. -/
  iota : Γ →* E
  /-- The element compressing the image of `Γ`. -/
  t : E
  /-- The root element centralized by the Kazhdan image. -/
  c : E
  /-- Property `(T)` for the source. -/
  kazhdan : HasKazhdanPropertyT.{v, v} Γ
  /-- Conjugation by `t` carries `ι(Γ)` back into `ι(Γ)`. -/
  compresses : ∀ γ : Γ, ∃ δ : Γ, t * iota γ * t⁻¹ = iota δ
  /-- The root centralizes the image of `Γ`. -/
  comm_c : ∀ γ : Γ, Commute c (iota γ)

namespace KazhdanCompressionCore

variable {Γ : Type v} {E : Type u} [Group Γ] [Group E]

/-- The transported root `d = t c t⁻¹`. -/
def transported (C : KazhdanCompressionCore Γ E) : E :=
  C.t * C.c * C.t⁻¹

/-- The pointwise compression defects `[d, ι(γ)]`. -/
def defectSet (C : KazhdanCompressionCore Γ E) : Set E :=
  Set.range fun γ : Γ ↦ ⁅C.transported, C.iota γ⁆

/-- The normal closure of the pointwise compression defects. -/
def defectNormal (C : KazhdanCompressionCore Γ E) : Subgroup E :=
  Subgroup.normalClosure C.defectSet

instance defectNormal_normal (C : KazhdanCompressionCore Γ E) :
    C.defectNormal.Normal :=
  Subgroup.normalClosure_normal

/-- Every pointwise compression defect belongs to its normal closure. -/
theorem defect_mem_defectNormal (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    ⁅C.transported, C.iota γ⁆ ∈ C.defectNormal :=
  Subgroup.subset_normalClosure ⟨γ, rfl⟩

/-- A homomorphism killing all pointwise defects kills their normal closure. -/
theorem defectNormal_le_ker {H : Type*} [Group H]
    (C : KazhdanCompressionCore Γ E) (rho : E →* H)
    (hdefect : ∀ γ : Γ, rho ⁅C.transported, C.iota γ⁆ = 1) :
    C.defectNormal ≤ rho.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨γ, rfl⟩
  exact MonoidHom.mem_ker.mpr (hdefect γ)

/-- A subgroup inside the defect normal closure is killed pointwise whenever
the generating defects are killed. -/
theorem map_eq_one_of_mem_of_defects_eq_one {H : Type*} [Group H]
    (C : KazhdanCompressionCore Γ E) (rho : E →* H)
    (hdefect : ∀ γ : Γ, rho ⁅C.transported, C.iota γ⁆ = 1)
    (F : Subgroup E) (hF : F ≤ C.defectNormal) (f : F) :
    rho f = 1 :=
  MonoidHom.mem_ker.mp (C.defectNormal_le_ker rho hdefect (hF f.property))

end KazhdanCompressionCore
end GroupApproximation
