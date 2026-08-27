import GroupApproximation.Higman.OmegaFatSlimCanonicalTwo
import GroupApproximation.Higman.OmegaTowerStageTwo
import GroupApproximation.Higman.OmegaFatSelectedCutter

/-!
# The full slim first stage inside the fat first stage

The second pushed-edge comap closes the third central HNN subextension.  The
resulting injection transports the row carrier, all three stable generators,
and the block link elements literally.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

theorem slimFatIsSubextension3 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (push2 (fatOutside m)))
    (MulEquiv.refl (push2 (rowOut m))) (slimFatCanonical2 m) where
  inj := slimFatCanonical2_injective m
  memA z := by
    change (z : Cent2 (rowOut m)) ∈
      (push2 (fatOutside m)).comap (slimFatCanonical2 m)
    rw [fatPush2_comap_slimFatCanonical2]
    exact z.property
  satA z hz := by
    rw [← fatPush2_comap_slimFatCanonical2]
    exact hz
  satB z hz := by
    rw [← fatPush2_comap_slimFatCanonical2]
    exact hz
  compat z hz := by simp

noncomputable def slimFatCanonical3 (m : ℕ) :
    Cent3 (rowOut m) →* FatCent3 m :=
  HNNSubextension.canonical (slimFatIsSubextension3 m)

theorem slimFatCanonical3_injective (m : ℕ) :
    Function.Injective (slimFatCanonical3 m) :=
  HNNSubextension.injective_of_isSubextensionHom (slimFatIsSubextension3 m)
    (HNNSubextension.isSubextensionHom_canonical (slimFatIsSubextension3 m))

@[simp] theorem slimFatCanonical3_of (m : ℕ) (x : Cent2 (rowOut m)) :
    slimFatCanonical3 m (of x) = of (slimFatCanonical2 m x) :=
  (HNNSubextension.isSubextensionHom_canonical
    (slimFatIsSubextension3 m)).map_of x

@[simp] theorem slimFatCanonical3_t (m : ℕ) :
    slimFatCanonical3 m (t : Cent3 (rowOut m)) =
      (t : FatCent3 m) :=
  (HNNSubextension.isSubextensionHom_canonical
    (slimFatIsSubextension3 m)).map_t

@[simp] theorem slimFatCanonical3_emb3 (m : ℕ) (x : Row.F₀) :
    slimFatCanonical3 m (emb3 (rowOut m) x) = fatCent3Emb m x := by
  simp [emb3, emb2, emb1, fatCent3Emb]

@[simp] theorem slimFatCanonical3_gen1 (m : ℕ) :
    slimFatCanonical3 m (gen1 (rowOut m)) = gen1 (fatOutside m) := by
  simp [gen1]

@[simp] theorem slimFatCanonical3_gen2 (m : ℕ) :
    slimFatCanonical3 m (gen2 (rowOut m)) = gen2 (fatOutside m) := by
  simp [gen2]

@[simp] theorem slimFatCanonical3_gen3 (m : ℕ) :
    slimFatCanonical3 m (gen3 (rowOut m)) = gen3 (fatOutside m) := by
  simp [gen3]

theorem slimFatCanonical3_comp_genHom (m : ℕ) :
    (slimFatCanonical3 m).comp (genHom (rowOut m)) =
      genHom (fatOutside m) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;> simp [genHom]

@[simp] theorem slimFatCanonical3_slimGenCode (m : ℕ) (beta : E) :
    slimFatCanonical3 m (slimGenCode m beta) = fatGenCode m beta := by
  rw [slimGenCode, fatGenCode, ← MonoidHom.comp_apply,
    slimFatCanonical3_comp_genHom]

@[simp] theorem slimFatCanonical3_slimBaseCode (m : ℕ) (beta : E) :
    slimFatCanonical3 m (slimBaseCode m beta) =
      fatCent3Emb m (Row.basisHom (elt beta)) := by
  simp [slimBaseCode]

@[simp] theorem slimFatCanonical3_slimLinkElem (m : ℕ) (beta : E) :
    slimFatCanonical3 m (slimLinkElem m beta) =
      fatGenCode m beta *
        (fatCent3Emb m (Row.basisHom (elt beta)))⁻¹ := by
  simp [slimLinkElem]

end Omega
end Higman
end GroupApproximation
