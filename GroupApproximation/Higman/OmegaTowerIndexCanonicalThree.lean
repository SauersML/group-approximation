import GroupApproximation.Higman.OmegaTowerIndexCanonicalTwo
import GroupApproximation.Higman.OmegaTowerStageTwo

/-!
# The index-row subextension of the full three-stage Omega tower

The second subgroup preimage identity gives the final HNN subextension.  The
canonical embedding constructed here transports the restricted base, the
three stable generators, and the complete selected link code to their existing
counterparts in the slim row tower.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

theorem indexIsSubextension3 (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (push2 (rowOut m)))
    (MulEquiv.refl (indexPush2 m)) (indexCanonical2 m) where
  inj := indexCanonical2_injective m
  memA z := by
    change (z : IndexCent2 m) ∈
      (push2 (rowOut m)).comap (indexCanonical2 m)
    rw [push2_comap_indexCanonical2]
    exact z.property
  satA z hz := by
    rw [← push2_comap_indexCanonical2]
    exact hz
  satB z hz := by
    rw [← push2_comap_indexCanonical2]
    exact hz
  compat z hz := by simp

noncomputable def indexCanonical3 (m : ℕ) :
    IndexCent3 m →* Cent3 (rowOut m) :=
  HNNSubextension.canonical (indexIsSubextension3 m)

theorem indexCanonical3_injective (m : ℕ) :
    Function.Injective (indexCanonical3 m) :=
  HNNSubextension.injective_of_isSubextensionHom (indexIsSubextension3 m)
    (HNNSubextension.isSubextensionHom_canonical (indexIsSubextension3 m))

@[simp] theorem indexCanonical3_of (m : ℕ) (z : IndexCent2 m) :
    indexCanonical3 m (of z) = of (indexCanonical2 m z) :=
  (HNNSubextension.isSubextensionHom_canonical
    (indexIsSubextension3 m)).map_of z

@[simp] theorem indexCanonical3_t (m : ℕ) :
    indexCanonical3 m (t : IndexCent3 m) =
      (t : Cent3 (rowOut m)) :=
  (HNNSubextension.isSubextensionHom_canonical
    (indexIsSubextension3 m)).map_t

@[simp] theorem indexCanonical3_indexEmb3 (m : ℕ) (w : FreeGroup ℤ) :
    indexCanonical3 m (indexEmb3 m w) =
      emb3 (rowOut m) (Row.basisHom w) := by
  simp [indexEmb3, indexEmb2, indexEmb1, emb3, emb2, emb1]

@[simp] theorem indexCanonical3_indexGen1 (m : ℕ) :
    indexCanonical3 m (indexGen1 m) = gen1 (rowOut m) := by
  simp [indexGen1, gen1]

@[simp] theorem indexCanonical3_indexGen2 (m : ℕ) :
    indexCanonical3 m (indexGen2 m) = gen2 (rowOut m) := by
  simp [indexGen2, gen2]

@[simp] theorem indexCanonical3_indexGen3 (m : ℕ) :
    indexCanonical3 m (indexGen3 m) = gen3 (rowOut m) := by
  simp [indexGen3, gen3]

theorem indexCanonical3_comp_indexGenHom (m : ℕ) :
    (indexCanonical3 m).comp (indexGenHom m) = genHom (rowOut m) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;> simp [indexGenHom, genHom]

@[simp] theorem indexCanonical3_indexGenHom (m : ℕ) (x : F₃) :
    indexCanonical3 m (indexGenHom m x) = genHom (rowOut m) x := by
  rw [← MonoidHom.comp_apply, indexCanonical3_comp_indexGenHom]

@[simp] theorem indexCanonical3_indexBaseCode (m : ℕ) (beta : E) :
    indexCanonical3 m (indexBaseCode m beta) = slimBaseCode m beta := by
  simp [indexBaseCode, slimBaseCode]

@[simp] theorem indexCanonical3_indexGenCode (m : ℕ) (beta : E) :
    indexCanonical3 m (indexGenCode m beta) = slimGenCode m beta := by
  simp [indexGenCode, slimGenCode]

@[simp] theorem indexCanonical3_indexLinkElem (m : ℕ) (beta : E) :
    indexCanonical3 m (indexLinkElem m beta) = slimLinkElem m beta := by
  simp [indexLinkElem, slimLinkElem]

end Omega
end Higman
end GroupApproximation
