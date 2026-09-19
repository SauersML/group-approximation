import GroupApproximation.Algebra.HNNSubextension
import GroupApproximation.Higman.OmegaTowerLowStableProjection

/-!
# The index-row subextension of the first Omega stage

The free row basis identifies the tail subgroup on integer indices with the
right-tail row subgroup.  Hence the first restricted central HNN extension is
a literal HNN subextension of the first row stage.  This file packages the
canonical embedding and records the exact preimage of the subgroup pushed to
the second stage.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open HNNExtension

/-- The free row basis presents the tail-index central HNN extension as a
subextension of the right-tail row central HNN extension. -/
theorem indexIsSubextension1 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (rowOut m)) (MulEquiv.refl (tailIndexSub m))
    Row.basisHom where
  inj := Row.basisHom_injective
  memA z := (basisHom_mem_rowOut_iff m z).2 z.property
  satA z hz := (basisHom_mem_rowOut_iff m z).1 hz
  satB z hz := (basisHom_mem_rowOut_iff m z).1 hz
  compat z hz := by simp

/-- The canonical first-stage embedding induced by the free row basis. -/
noncomputable def indexCanonical1 (m : ℕ) :
    IndexCent1 m →* Cent1 (rowOut m) :=
  HNNSubextension.canonical (indexIsSubextension1 m)

theorem indexCanonical1_injective (m : ℕ) :
    Function.Injective (indexCanonical1 m) :=
  HNNSubextension.injective_of_isSubextensionHom (indexIsSubextension1 m)
    (HNNSubextension.isSubextensionHom_canonical (indexIsSubextension1 m))

@[simp] theorem indexCanonical1_of (m : ℕ) (w : FreeGroup ℤ) :
    indexCanonical1 m (of w) = of (Row.basisHom w) :=
  (HNNSubextension.isSubextensionHom_canonical
    (indexIsSubextension1 m)).map_of w

@[simp] theorem indexCanonical1_t (m : ℕ) :
    indexCanonical1 m (t : IndexCent1 m) =
      (t : Cent1 (rowOut m)) :=
  (HNNSubextension.isSubextensionHom_canonical
    (indexIsSubextension1 m)).map_t

/-- Pulling the associated subgroup for the second row stage back through the
canonical first-stage embedding gives exactly the locally pushed tail-index
subgroup.  This saturation identity is the input for the second canonical HNN
embedding. -/
theorem push1_comap_indexCanonical1 (m : ℕ) :
    (push1 (rowOut m)).comap (indexCanonical1 m) = indexPush1 m := by
  ext x
  constructor
  · intro hx
    change indexCanonical1 m x ∈ push1 (rowOut m) at hx
    unfold push1 at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [rowOut_eq_map_indexSub] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    change w ∈ tailIndexSub m at hw
    have hxw : x = indexEmb1 m w := indexCanonical1_injective m (by
      rw [indexEmb1, indexCanonical1_of]
      exact hxy.symm)
    rw [hxw]
    exact ⟨w, hw, rfl⟩
  · intro hx
    unfold indexPush1 at hx
    obtain ⟨w, hw, rfl⟩ := hx
    change indexCanonical1 m (indexEmb1 m w) ∈ push1 (rowOut m)
    rw [indexEmb1, indexCanonical1_of]
    exact ⟨Row.basisHom w, (basisHom_mem_rowOut_iff m w).2 hw, rfl⟩

end Omega
end Higman
end GroupApproximation
