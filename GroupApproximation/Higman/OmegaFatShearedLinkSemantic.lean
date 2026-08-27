import GroupApproximation.Higman.OmegaFatSlimCanonicalThree
import GroupApproximation.Higman.OmegaTowerStageTwoBritton

/-!
# The sheared Omega link in the fat semantic base

The genuine first-stage embedding does not send `g_beta b_beta^-1` to the
unsheared paired-return graph.  This file names the correct semantic target
and records its exact free-word parametrization.  These are the input
identities for the finite matched cutter; no finite witness is postulated
here.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- The natural injective semantic-base map retaining both the genuine
first-stage embedding and the row coordinate. -/
noncomputable def slimFatSemanticBaseEmb (m : ℕ) :
    Cent3 (rowOut m) →* FatCent3 m × F₃ :=
  (slimFatCanonical3 m).prod
    (rowIntoF3.comp (baseRet3 (rowOut m)))

theorem slimFatSemanticBaseEmb_injective (m : ℕ) :
    Function.Injective (slimFatSemanticBaseEmb m) := by
  intro x y hxy
  apply slimFatCanonical3_injective m
  exact congrArg Prod.fst hxy

/-- Evaluation of block-link words in the correct sheared semantic base. -/
noncomputable def fatShearedLinkLift (m : ℕ) :
    FreeGroup ↥(blockSet m) →* FatCent3 m × F₃ :=
  (slimFatSemanticBaseEmb m).comp (slimLinkLift m)

theorem fatShearedLinkLift_injective (m : ℕ) :
    Function.Injective (fatShearedLinkLift m) :=
  (slimFatSemanticBaseEmb_injective m).comp (slimLinkLift_injective m)

/-- The actual block link which a finite fat cutter must cut out. -/
noncomputable def fatShearedBlockLink (m : ℕ) :
    Subgroup (FatCent3 m × F₃) :=
  (fatShearedLinkLift m).range

theorem fatShearedBlockLink_eq_map (m : ℕ) :
    fatShearedBlockLink m =
      (slimLink m).map (slimFatSemanticBaseEmb m) := by
  rw [fatShearedBlockLink, fatShearedLinkLift, MonoidHom.range_comp,
    slimLinkLift_range]

/-- The sheared block link has exactly the slim link as its preimage. -/
theorem fatShearedBlockLink_comap_slimFatSemanticBaseEmb (m : ℕ) :
    (fatShearedBlockLink m).comap (slimFatSemanticBaseEmb m) =
      slimLink m := by
  rw [fatShearedBlockLink_eq_map]
  exact Subgroup.comap_map_eq_self_of_injective
    (slimFatSemanticBaseEmb_injective m) _

@[simp] theorem slimFatSemanticBaseEmb_slimLinkElem
    (m : ℕ) (beta : E) :
    slimFatSemanticBaseEmb m (slimLinkElem m beta) =
      (fatGenCode m beta *
          (fatCent3Emb m (Row.basisHom (elt beta)))⁻¹,
        (bElt beta)⁻¹) := by
  apply Prod.ext
  · exact slimFatCanonical3_slimLinkElem m beta
  · simp only [slimFatSemanticBaseEmb, MonoidHom.prod_apply,
      MonoidHom.comp_apply, slimLinkElem, map_mul, map_inv, slimGenCode,
      slimBaseCode, ← MonoidHom.comp_apply, baseRet3_comp_genHom,
      baseRet3_emb3, one_mul]
    have h := DFunLike.congr_fun rowIntoF3_comp_basisHom (elt beta)
    change rowIntoF3 (Row.basisHom (elt beta)) = bElt beta at h
    rw [h]

theorem slimFatSemanticBaseEmb_slimLinkElem_mem
    {m : ℕ} {beta : E} (hbeta : beta ∈ blockSet m) :
    slimFatSemanticBaseEmb m (slimLinkElem m beta) ∈
      fatShearedBlockLink m := by
  rw [fatShearedBlockLink_eq_map]
  exact Subgroup.mem_map_of_mem (slimFatSemanticBaseEmb m)
    (slimLinkElem_mem hbeta)

end Omega
end Higman
end GroupApproximation
