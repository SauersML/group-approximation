import GroupApproximation.Higman.OmegaFatShearedLinkSemantic
import GroupApproximation.Higman.OmegaFiniteLinkGraph

/-!
# Obstruction to the current fat-link semantic embedding

The injective first-stage embedding naturally pairs the canonical fat copy
with the slim row retraction.  The current `fatBlockLink`, however, puts the
row inverse only in the product's second coordinate and has trivial original-
base retraction in its first coordinate.  Consequently even a single nonzero
slim link generator misses the fat cutter.  This is a literal obstruction,
not merely a missing proof of comap exactness.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq
open GroupApproximation.Higman.Conj (F₃)

/-- Every element of the present fat link graph has trivial original-base
retraction in its first coordinate. -/
theorem baseRet3_fst_eq_one_of_mem_fatBlockLink
    {m : ℕ} {z : FatCent3 m × F₃} (hz : z ∈ fatBlockLink m) :
    baseRet3 (fatOutside m) z.1 = 1 := by
  obtain ⟨p, -, rfl⟩ := hz
  have hcomp :=
    DFunLike.congr_fun (baseRet3_comp_genHom (fatOutside m)) (flipAHom p.1)
  change baseRet3 (fatOutside m)
      (genHom (fatOutside m) (flipAHom p.1)) = 1
  simpa using hcomp

theorem fatBaseRow_ne_one_of_block_ne_zero
    {m : ℕ} {beta : E} (hbeta : beta ≠ 0) :
    fatBaseEmb m (Row.basisHom (elt beta)) ≠ 1 := by
  intro h
  have hrow : Row.basisHom (elt beta) = 1 := by
    apply (rowOutWitness m).witness.emb_injective
    rw [map_one]
    exact h
  have helt : elt beta = 1 := by
    apply Row.basisHom_injective
    simpa using hrow
  exact hbeta (elt_injective (by simpa using helt))

/-- A nonzero slim link generator does not even map into the current fat
block-link cutter under the natural injective semantic-base embedding. -/
theorem slimFatSemanticBaseEmb_slimLinkElem_not_mem_fatBlockLink
    {m : ℕ} {beta : E} (hbeta : beta ≠ 0) :
    slimFatSemanticBaseEmb m (slimLinkElem m beta) ∉ fatBlockLink m := by
  intro hmem
  have hgen :
      baseRet3 (fatOutside m) (genHom (fatOutside m) (aElt beta)) = 1 := by
    have hcomp :=
      DFunLike.congr_fun (baseRet3_comp_genHom (fatOutside m)) (aElt beta)
    simpa using hcomp
  have hret := baseRet3_fst_eq_one_of_mem_fatBlockLink hmem
  change baseRet3 (fatOutside m)
      (slimFatCanonical3 m (slimLinkElem m beta)) = 1 at hret
  rw [slimFatCanonical3_slimLinkElem, map_mul, map_inv, fatGenCode, hgen,
    fatCent3Emb, MonoidHom.comp_apply, baseRet3_emb3, one_mul,
    inv_eq_one] at hret
  exact fatBaseRow_ne_one_of_block_ne_zero hbeta hret

end Omega
end Higman
end GroupApproximation
