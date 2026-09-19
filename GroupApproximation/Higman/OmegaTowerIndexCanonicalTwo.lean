import GroupApproximation.Higman.OmegaTowerIndexCanonicalOne

/-!
# The index-row subextension of the second Omega stage

The stage-one subgroup preimage identity supplies precisely the two
saturation clauses for a second application of the HNN subextension theorem.
The resulting stage-two embedding again has the exact subgroup preimage needed
to adjoin the third stable letter.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open HNNExtension

theorem indexIsSubextension2 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (push1 (rowOut m)))
    (MulEquiv.refl (indexPush1 m)) (indexCanonical1 m) where
  inj := indexCanonical1_injective m
  memA z := by
    change (z : IndexCent1 m) ∈
      (push1 (rowOut m)).comap (indexCanonical1 m)
    rw [push1_comap_indexCanonical1]
    exact z.property
  satA z hz := by
    rw [← push1_comap_indexCanonical1]
    exact hz
  satB z hz := by
    rw [← push1_comap_indexCanonical1]
    exact hz
  compat z hz := by simp

noncomputable def indexCanonical2 (m : ℕ) :
    IndexCent2 m →* Cent2 (rowOut m) :=
  HNNSubextension.canonical (indexIsSubextension2 m)

theorem indexCanonical2_injective (m : ℕ) :
    Function.Injective (indexCanonical2 m) :=
  HNNSubextension.injective_of_isSubextensionHom (indexIsSubextension2 m)
    (HNNSubextension.isSubextensionHom_canonical (indexIsSubextension2 m))

@[simp] theorem indexCanonical2_of (m : ℕ) (z : IndexCent1 m) :
    indexCanonical2 m (of z) = of (indexCanonical1 m z) :=
  (HNNSubextension.isSubextensionHom_canonical
    (indexIsSubextension2 m)).map_of z

@[simp] theorem indexCanonical2_t (m : ℕ) :
    indexCanonical2 m (t : IndexCent2 m) =
      (t : Cent2 (rowOut m)) :=
  (HNNSubextension.isSubextensionHom_canonical
    (indexIsSubextension2 m)).map_t

theorem push2_comap_indexCanonical2 (m : ℕ) :
    (push2 (rowOut m)).comap (indexCanonical2 m) = indexPush2 m := by
  ext x
  constructor
  · intro hx
    change indexCanonical2 m x ∈ push2 (rowOut m) at hx
    unfold push2 at hx
    obtain ⟨y, hy, hxy⟩ := hx
    unfold push1 at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [rowOut_eq_map_indexSub] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    change w ∈ tailIndexSub m at hw
    have hxw : x = (of : IndexCent1 m →* IndexCent2 m) (indexEmb1 m w) :=
      indexCanonical2_injective m (by
        rw [indexCanonical2_of, indexEmb1, indexCanonical1_of]
        exact hxy.symm)
    rw [hxw]
    exact ⟨indexEmb1 m w, ⟨w, hw, rfl⟩, rfl⟩
  · intro hx
    unfold indexPush2 at hx
    obtain ⟨z, hz, rfl⟩ := hx
    change indexCanonical2 m (of z) ∈ push2 (rowOut m)
    rw [indexCanonical2_of]
    refine ⟨indexCanonical1 m z, ?_, rfl⟩
    change z ∈ (push1 (rowOut m)).comap (indexCanonical1 m)
    rw [push1_comap_indexCanonical1]
    exact hz

end Omega
end Higman
end GroupApproximation
