import GroupApproximation.Algebra.HNNSubextension
import GroupApproximation.Higman.OmegaTowerStages

/-!
# The slim first central stage inside the fat first central stage

The benign witness embeds the row carrier and cuts out the right-tail subgroup
exactly.  This is precisely the saturation datum for the first central HNN
subextension.  The base retractions then prove the exact preimage of the
pushed edge subgroup needed at the next central stage.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open HNNExtension

theorem slimFatIsSubextension1 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (fatOutside m)) (MulEquiv.refl (rowOut m))
    (fatBaseEmb m) where
  inj := (rowOutWitness m).witness.emb_injective
  memA z := by
    rw [← Subgroup.mem_comap, (rowOutWitness m).witness.comap_eq]
    exact z.property
  satA z hz := by
    rw [← (rowOutWitness m).witness.comap_eq]
    exact hz
  satB z hz := by
    rw [← (rowOutWitness m).witness.comap_eq]
    exact hz
  compat z hz := by simp

noncomputable def slimFatCanonical1 (m : ℕ) :
    Cent1 (rowOut m) →* Cent1 (fatOutside m) :=
  HNNSubextension.canonical (slimFatIsSubextension1 m)

theorem slimFatCanonical1_injective (m : ℕ) :
    Function.Injective (slimFatCanonical1 m) :=
  HNNSubextension.injective_of_isSubextensionHom (slimFatIsSubextension1 m)
    (HNNSubextension.isSubextensionHom_canonical (slimFatIsSubextension1 m))

@[simp] theorem slimFatCanonical1_of (m : ℕ) (x : Row.F₀) :
    slimFatCanonical1 m (of x) = of (fatBaseEmb m x) :=
  (HNNSubextension.isSubextensionHom_canonical
    (slimFatIsSubextension1 m)).map_of x

@[simp] theorem slimFatCanonical1_t (m : ℕ) :
    slimFatCanonical1 m (t : Cent1 (rowOut m)) =
      (t : Cent1 (fatOutside m)) :=
  (HNNSubextension.isSubextensionHom_canonical
    (slimFatIsSubextension1 m)).map_t

theorem baseRet1_comp_slimFatCanonical1 (m : ℕ) :
    (baseRet1 (fatOutside m)).comp (slimFatCanonical1 m) =
      (fatBaseEmb m).comp (baseRet1 (rowOut m)) := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine MonoidHom.ext fun x => ?_
    simp
  · simp

/-- The first pushed right-tail subgroup has exactly the expected preimage
through the canonical slim-to-fat embedding. -/
theorem fatPush1_comap_slimFatCanonical1 (m : ℕ) :
    (push1 (fatOutside m)).comap (slimFatCanonical1 m) = push1 (rowOut m) := by
  ext x
  constructor
  · intro hx
    change slimFatCanonical1 m x ∈ push1 (fatOutside m) at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hybase := congrArg (baseRet1 (fatOutside m)) hyx
    have hret := DFunLike.congr_fun (baseRet1_comp_slimFatCanonical1 m) x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hret
    have hyEq : y = fatBaseEmb m (baseRet1 (rowOut m) x) := by
      simpa using hybase.trans hret
    have hsource : baseRet1 (rowOut m) x ∈ rowOut m := by
      rw [← (rowOutWitness m).witness.comap_eq]
      rwa [← hyEq]
    have hxbase : x = of (baseRet1 (rowOut m) x) := by
      apply slimFatCanonical1_injective m
      rw [slimFatCanonical1_of, hyEq.symm]
      exact hyx.symm
    rw [hxbase]
    exact ⟨baseRet1 (rowOut m) x, hsource, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    change slimFatCanonical1 m (of y) ∈ push1 (fatOutside m)
    rw [slimFatCanonical1_of]
    exact ⟨fatBaseEmb m y, by
      rw [← Subgroup.mem_comap, (rowOutWitness m).witness.comap_eq]
      exact hy, rfl⟩

end Omega
end Higman
end GroupApproximation
