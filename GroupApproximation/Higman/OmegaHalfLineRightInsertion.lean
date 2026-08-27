import GroupApproximation.Higman.OmegaTowerDescent
import GroupApproximation.Higman.SwapCarrierWitness

/-!
# Canonical right insertion for the one-sided Omega construction

The refuted two-sided Omega tower allowed a selected window block to be
inserted on the wrong side of a negative row word.  On the nonnegative
half-line the relevant row word is supported at indices at least `m`, while a
window block is supported in `[0,m)`.  The sorted sequence code therefore has
the literal order

    `b_(beta + l) = b_beta * b_l`.

This file records that arithmetic boundary and combines it with the exact
one-letter seam theorem from `OmegaTowerDescent`.  The resulting theorem is
the concrete productive edge calculation needed by an asymmetric HNN
construction of `omegaGE`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- A block supported in `[0,m)` precedes every word supported in the right
tail `[m,infinity)` in the canonical row order. -/
theorem block_support_lt_rightTail
    {m : ℕ} {beta l : E} (hbeta : beta ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    ∀ i ∈ beta.support, ∀ j ∈ l.support, i < j := by
  intro i hi j hj
  have hibeta : beta i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hiwindow : i ∈ Finset.Ico (0 : ℤ) (m : ℤ) := by
    by_contra hout
    exact hibeta (hbeta i hout)
  have him : i < (m : ℤ) := (Finset.mem_Ico.mp hiwindow).2
  have hmj : (m : ℤ) ≤ j := hl j (Finsupp.mem_support_iff.mp hj)
  exact lt_of_lt_of_le him hmj

/-- Canonical sequence coding is multiplicative when a window block is
followed by a right-tail sequence. -/
theorem bElt_add_block_rightTail
    {m : ℕ} {beta l : E} (hbeta : beta ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    bElt (beta + l) = bElt beta * bElt l :=
  bElt_add_of_lt (block_support_lt_rightTail hbeta hl)

/-- Inserting a window block before a right tail gives the canonical
conjugate indexed by the sum of the two sequences. -/
theorem aElt_add_block_rightTail
    {m : ℕ} {beta l : E} (hbeta : beta ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    aElt (beta + l) = (bElt l)⁻¹ * aElt beta * bElt l := by
  unfold aElt
  rw [bElt_add_block_rightTail hbeta hl]
  group

/-- **Concrete productive one-sided seam.**  The selected generator for a
window block acts on a right-tail code by prepending that block in canonical
sequence order. -/
theorem slimGen_conj_aElt_eq_add_of_rightTail
    {m : ℕ} {beta l : E} (hbeta : beta ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    (slimPiOf m (slimGenCode m beta))⁻¹ * slimPiF3Hom m (aElt l) *
        slimPiOf m (slimGenCode m beta) =
      slimPiF3Hom m (aElt (beta + l)) := by
  rw [slimGen_conj_aElt_eq_rowConj_of_rightTail hbeta hl,
    aElt_add_block_rightTail hbeta hl, map_mul, map_mul, map_inv]

end Omega
end Higman
end GroupApproximation
