import GroupApproximation.Algebra.HNNSubextension
import GroupApproximation.Higman.OmegaTowerStages
import GroupApproximation.Higman.OmegaTowerDescent

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

/-- **The benign witness's defining equation, at the fat base.**  The cutter
`fatOutside m` is `L`, the embedding `fatBaseEmb m` is `emb`, and the witness
says exactly that `L` pulls back to the right-tail subgroup. -/
theorem fatOutside_comap_fatBaseEmb (m : ℕ) :
    (fatOutside m).comap (fatBaseEmb m) = rowOut m :=
  (rowOutWitness m).witness.comap_eq

/-- The pointwise reading of `fatOutside_comap_fatBaseEmb`.  Stated as an
`Iff` rather than used through `rw`, because `rowOut m` occurs as a *type
index* in the terms this file manipulates, where rewriting it is not
type-correct. -/
theorem mem_fatOutside_iff {m : ℕ} {x : Row.F₀} :
    fatBaseEmb m x ∈ fatOutside m ↔ x ∈ rowOut m := by
  constructor
  · intro h
    rw [← fatOutside_comap_fatBaseEmb]
    exact h
  · intro h
    rw [← fatOutside_comap_fatBaseEmb] at h
    exact h

theorem slimFatIsSubextension1 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (fatOutside m)) (MulEquiv.refl (rowOut m))
    (fatBaseEmb m) where
  inj := (rowOutWitness m).witness.emb_injective
  memA z := mem_fatOutside_iff.mpr z.property
  satA _ hz := mem_fatOutside_iff.mp hz
  satB _ hz := mem_fatOutside_iff.mp hz
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
    have hybase : baseRet1 (fatOutside m) (of y)
        = baseRet1 (fatOutside m) (slimFatCanonical1 m x) :=
      congrArg (fun w : Cent1 (fatOutside m) => baseRet1 (fatOutside m) w) hyx
    have hret := DFunLike.congr_fun (baseRet1_comp_slimFatCanonical1 m) x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hret
    have hyEq : y = fatBaseEmb m (baseRet1 (rowOut m) x) :=
      (baseRet1_of (fatOutside m) y).symm.trans (hybase.trans hret)
    have hfat : fatBaseEmb m (baseRet1 (rowOut m) x) ∈ fatOutside m := by
      rw [← hyEq]
      exact hy
    have hsource : baseRet1 (rowOut m) x ∈ rowOut m := mem_fatOutside_iff.mp hfat
    have hxbase : x = of (baseRet1 (rowOut m) x) := by
      apply slimFatCanonical1_injective m
      rw [slimFatCanonical1_of, ← hyEq]
      exact hyx.symm
    rw [hxbase]
    exact mem_push1 hsource
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    change slimFatCanonical1 m (of y) ∈ push1 (fatOutside m)
    rw [slimFatCanonical1_of]
    exact mem_push1 (mem_fatOutside_iff.mpr hy)

end Omega
end Higman
end GroupApproximation
