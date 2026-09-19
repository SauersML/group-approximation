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

/-- The pointwise reading of `fatPush1_comap_slimFatCanonical1`.  Stated as an
`Iff` rather than used through `rw`, because `push1 (rowOut m)` occurs as a
*type index* in the terms this file manipulates --- it is the associated
subgroup of the second central stage --- where rewriting it is not
type-correct. -/
theorem mem_fatPush1_iff {m : ℕ} {z : Cent1 (rowOut m)} :
    slimFatCanonical1 m z ∈ push1 (fatOutside m) ↔ z ∈ push1 (rowOut m) := by
  constructor
  · intro h
    rw [← fatPush1_comap_slimFatCanonical1]
    exact h
  · intro h
    rw [← fatPush1_comap_slimFatCanonical1] at h
    exact h

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
    have hybase : baseRet1 (push1 (fatOutside m)) (of y)
        = baseRet1 (push1 (fatOutside m)) (slimFatCanonical2 m x) :=
      congrArg (fun w : Cent2 (fatOutside m) =>
        baseRet1 (push1 (fatOutside m)) w) hyx
    have hret := DFunLike.congr_fun (centralRet2_comp_slimFatCanonical2 m) x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hret
    have hyEq : y = slimFatCanonical1 m
        (baseRet1 (push1 (rowOut m)) x) :=
      (baseRet1_of (push1 (fatOutside m)) y).symm.trans (hybase.trans hret)
    have hfat : slimFatCanonical1 m (baseRet1 (push1 (rowOut m)) x)
        ∈ push1 (fatOutside m) := by
      rw [← hyEq]
      exact hy
    have hsource : baseRet1 (push1 (rowOut m)) x ∈ push1 (rowOut m) :=
      mem_fatPush1_iff.mp hfat
    have hxbase : x = of (baseRet1 (push1 (rowOut m)) x) := by
      apply slimFatCanonical2_injective m
      rw [slimFatCanonical2_of, ← hyEq]
      exact hyx.symm
    rw [hxbase]
    exact ⟨baseRet1 (push1 (rowOut m)) x, hsource, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    change slimFatCanonical2 m (of y) ∈ push2 (fatOutside m)
    rw [slimFatCanonical2_of]
    exact ⟨slimFatCanonical1 m y, mem_fatPush1_iff.mpr hy, rfl⟩

end Omega
end Higman
end GroupApproximation
