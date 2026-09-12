import GroupApproximation.Sofic.DirectSumAmplification
import GroupApproximation.Sofic.OperatorMFLocalNormalization

/-!
# Operator-MF is closed under direct products

This file proves the direct-product permanence theorem from the repository's
finite-test-set characterization of operator-MF.  Given local models for two
groups, put the two matrices on diagonal blocks.  Multiplication defects then
combine by `max`, and a distinct pair is separated in at least one block.

The proof is entirely internal: it uses the already formalized block-diagonal
operator-norm identity and the already proved equivalence between the literal
cofinite-corona definition and normalized local models.  No C-star-algebra
permanence theorem is assumed.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u v

noncomputable section

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Normalized local operator-norm approximability is closed under direct
products.  The product model is the block diagonal of the two supplied
models. -/
theorem IsNormApproximable.prod
    (hG : IsNormApproximable G 1) (hH : IsNormApproximable H 1) :
    IsNormApproximable (G × H) 1 := by
  classical
  intro F ε hε
  let FG : Finset G := F.image Prod.fst
  let FH : Finset H := F.image Prod.snd
  obtain ⟨MG⟩ := hG FG ε hε
  obtain ⟨MH⟩ := hH FH ε hε
  refine ⟨{
    carrier := blockSumModel MG.carrier MH.carrier
    nonempty := ?_
    map := fun q ↦ blockDiagMatrix MG.carrier MH.carrier
      (MG.map q.1) (MH.map q.2)
    isUnitary := ?_
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [Fintype.card_pos_iff]
    letI : Nonempty MG.carrier := Fintype.card_pos_iff.mp MG.nonempty
    exact ⟨Sum.inl (Classical.choice inferInstance)⟩
  · intro q
    exact blockDiagMatrix_mem_unitaryGroup MG.carrier MH.carrier
      (MG.isUnitary q.1) (MH.isUnitary q.2)
  · intro q hq r hr
    have hqG : q.1 ∈ FG := by
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hrG : r.1 ∈ FG := by
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    have hqH : q.2 ∈ FH := by
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hrH : r.2 ∈ FH := by
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    change
      ‖blockDiagMatrix MG.carrier MH.carrier
          (MG.map (q * r).1) (MH.map (q * r).2) -
        blockDiagMatrix MG.carrier MH.carrier (MG.map q.1) (MH.map q.2) *
          blockDiagMatrix MG.carrier MH.carrier (MG.map r.1) (MH.map r.2)‖ ≤ ε
    rw [blockDiagMatrix_mul, blockDiagMatrix_sub, l2_opNorm_blockDiag]
    exact max_le
      (by simpa using MG.multiplicative q.1 hqG r.1 hrG)
      (by simpa using MH.multiplicative q.2 hqH r.2 hrH)
  · intro q hq r hr hqr
    have hqG : q.1 ∈ FG := Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hrG : r.1 ∈ FG := Finset.mem_image.mpr ⟨r, hr, rfl⟩
    have hqH : q.2 ∈ FH := Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hrH : r.2 ∈ FH := Finset.mem_image.mpr ⟨r, hr, rfl⟩
    change 1 ≤
      ‖blockDiagMatrix MG.carrier MH.carrier (MG.map q.1) (MH.map q.2) -
        blockDiagMatrix MG.carrier MH.carrier (MG.map r.1) (MH.map r.2)‖
    rw [blockDiagMatrix_sub, l2_opNorm_blockDiag]
    by_cases hfirst : q.1 = r.1
    · have hsecond : q.2 ≠ r.2 := by
        intro hs
        exact hqr (Prod.ext hfirst hs)
      exact (MH.separated q.2 hqH r.2 hrH hsecond).trans
        (le_max_right _ _)
    · exact (MG.separated q.1 hqG r.1 hrG hfirst).trans
        (le_max_left _ _)

/-- **Direct-product permanence for the literal MF predicate.**  The product
of two countable operator-MF groups is operator-MF. -/
theorem IsOperatorMF.prod [Countable G] [Countable H]
    (hG : IsOperatorMF G) (hH : IsOperatorMF H) :
    IsOperatorMF (G × H) := by
  apply OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
  exact (OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mp hG).prod
    (OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mp hH)

end

end GroupApproximation
