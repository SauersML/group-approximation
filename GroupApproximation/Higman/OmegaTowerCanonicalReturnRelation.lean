import GroupApproximation.Higman.OmegaTowerRightTailSubgroup

/-!
# The four canonical outcomes of an Omega return

The binary free-product normal form leaves four sequence-level outcomes: no
change, prepending one selected zeroth block, removing one selected zeroth
block, or replacing one selected zeroth block by another while retaining a
common right tail.  This file records that literal disjunction and proves
that every outcome preserves the block language.  The normal-form layer can
therefore finish by producing the disjunction, without repeating block
arithmetic.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- The sequence-level alternatives left by the full-code free-product
normal form. -/
def CanonicalReturnRelation (m : ℕ) (B : Set E) (l f : E) : Prop :=
  l = f ∨
    (∃ beta : E, beta ∈ B ∩ blockSet m ∧
      rightTailSet m l ∧ f = beta + l) ∨
    (∃ beta : E, beta ∈ B ∩ blockSet m ∧
      rightTailSet m f ∧ l = beta + f) ∨
    (∃ beta gamma t : E, beta ∈ B ∩ blockSet m ∧
      gamma ∈ B ∩ blockSet m ∧ rightTailSet m t ∧
        l = beta + t ∧ f = gamma + t)

/-- Every normal-form outcome carries an Omega sequence to another Omega
sequence. -/
theorem omega_mem_of_canonicalReturnRelation
    {m : ℕ} (hm : 0 < m) {B : Set E} (h0 : (0 : E) ∈ B)
    {l f : E} (hl : l ∈ omegaOp m B)
    (hreturn : CanonicalReturnRelation m B l f) :
    f ∈ omegaOp m B := by
  rcases hreturn with hsame | hadd | hremove | hselected
  · rwa [← hsame]
  · obtain ⟨beta, hbeta, hlTail, rfl⟩ := hadd
    exact add_rightTail_mem_omegaOp hm hbeta hlTail hl
  · obtain ⟨beta, hbeta, hfTail, rfl⟩ := hremove
    exact rightTail_mem_omegaOp_of_add hm h0 hbeta.2 hfTail hl
  · obtain ⟨beta, gamma, t, hbeta, hgamma, htTail, rfl, rfl⟩ := hselected
    have htOmega : t ∈ omegaOp m B :=
      rightTail_mem_omegaOp_of_add hm h0 hbeta.2 htTail hl
    exact add_rightTail_mem_omegaOp hm hgamma htTail htOmega

end Omega
end Higman
end GroupApproximation
