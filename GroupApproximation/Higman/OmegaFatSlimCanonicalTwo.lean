import GroupApproximation.Higman.OmegaFatSlimCanonicalOne

/-!
# The slim second central stage inside the fat second central stage

The exact first pushed-edge comap is the saturation datum for the next HNN
subextension.  Its base retraction again identifies the precise preimage of
the edge pushed to the third central stage.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open HNNExtension

theorem slimFatIsSubextension2 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (push1 (fatOutside m)))
    (MulEquiv.refl (push1 (rowOut m))) (slimFatCanonical1 m) where
  inj := slimFatCanonical1_injective m
  memA z := by
    change (z : Cent1 (rowOut m)) ∈
      (push1 (fatOutside m)).comap (slimFatCanonical1 m)
    rw [fatPush1_comap_slimFatCanonical1]
    exact z.property
  satA z hz := by
    rw [← fatPush1_comap_slimFatCanonical1]
    exact hz
  satB z hz := by
    rw [← fatPush1_comap_slimFatCanonical1]
    exact hz
  compat z hz := by simp

noncomputable def slimFatCanonical2 (m : ℕ) :
    Cent2 (rowOut m) →* Cent2 (fatOutside m) :=
  HNNSubextension.canonical (slimFatIsSubextension2 m)

theorem slimFatCanonical2_injective (m : ℕ) :
    Function.Injective (slimFatCanonical2 m) :=
  HNNSubextension.injective_of_isSubextensionHom (slimFatIsSubextension2 m)
    (HNNSubextension.isSubextensionHom_canonical (slimFatIsSubextension2 m))

@[simp] theorem slimFatCanonical2_of (m : ℕ) (x : Cent1 (rowOut m)) :
    slimFatCanonical2 m (of x) = of (slimFatCanonical1 m x) :=
  (HNNSubextension.isSubextensionHom_canonical
    (slimFatIsSubextension2 m)).map_of x

@[simp] theorem slimFatCanonical2_t (m : ℕ) :
    slimFatCanonical2 m (t : Cent2 (rowOut m)) =
      (t : Cent2 (fatOutside m)) :=
  (HNNSubextension.isSubextensionHom_canonical
    (slimFatIsSubextension2 m)).map_t

theorem centralRet2_comp_slimFatCanonical2 (m : ℕ) :
    (baseRet1 (push1 (fatOutside m))).comp (slimFatCanonical2 m) =
      (slimFatCanonical1 m).comp (baseRet1 (push1 (rowOut m))) := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine MonoidHom.ext fun x => ?_
    simp
  · simp

theorem fatPush2_comap_slimFatCanonical2 (m : ℕ) :
    (push2 (fatOutside m)).comap (slimFatCanonical2 m) = push2 (rowOut m) := by
  ext x
  constructor
  · intro hx
    change slimFatCanonical2 m x ∈ push2 (fatOutside m) at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hybase := congrArg (baseRet1 (push1 (fatOutside m))) hyx
    have hret := DFunLike.congr_fun (centralRet2_comp_slimFatCanonical2 m) x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hret
    have hyEq : y = slimFatCanonical1 m
        (baseRet1 (push1 (rowOut m)) x) := by
      simpa using hybase.trans hret
    have hsource : baseRet1 (push1 (rowOut m)) x ∈ push1 (rowOut m) := by
      rw [← fatPush1_comap_slimFatCanonical1]
      rwa [← hyEq]
    have hxbase : x = of (baseRet1 (push1 (rowOut m)) x) := by
      apply slimFatCanonical2_injective m
      rw [slimFatCanonical2_of, hyEq.symm]
      exact hyx.symm
    rw [hxbase]
    exact ⟨baseRet1 (push1 (rowOut m)) x, hsource, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    change slimFatCanonical2 m (of y) ∈ push2 (fatOutside m)
    rw [slimFatCanonical2_of]
    exact ⟨slimFatCanonical1 m y, by
      rw [← Subgroup.mem_comap, fatPush1_comap_slimFatCanonical1]
      exact hy, rfl⟩

end Omega
end Higman
end GroupApproximation
