import GroupApproximation.Leavitt.LeavittRankEquivalence

/-!
# `R ≅ M₂(R)` and `EL₂(R) ≅ EL₄(R)` for a binary Leavitt family

`notes/rank-two-descent-note-2026-09-07.md`, §6:

> For `R = L_{𝔽₂}(1,2)`: `x ↦ (tᵢ x sⱼ)` is a ring isomorphism `R ≅ M₂(R)`, so
> `EL₂(R) ≅ EL₂(M₂(R)) = EL₄(R)` (cross-block roots are block-elementary; a
> within-block root is a Steinberg commutator of two cross-block roots through
> the other block).  So the headline transfers to `EL₂` without a rank-two
> `(T)` or normal-structure citation.

Both isomorphisms are already available in the tree, for every ring carrying a
binary Leavitt family and not only for `L_{𝔽₂}(1,2)`.  This module names them
at the shape the note uses.

* The ring isomorphism is the two-leaf case of prefix self-similarity,
  `LeavittFamily.prefixRingEquiv` at the comb code with two leaves.  The note
  writes the map `R → M₂(R)`; the repository's primitive is its inverse
  `M₂(R) → R`, `A ↦ ∑ᵢⱼ S_i A_ij T_j` with `S`, `T` the cylinder words of the
  code, so `ringEquivMatrixTwo` is that inverse turned around.

* The group isomorphism is **not** obtained here through the note's block
  argument.  `LeavittFamily.rankSuccEquiv` already identifies *every* pair of
  positive elementary ranks over a ring with a binary Leavitt family, by the
  same prefix-code route, and `EL₂(R) ≅ EL₄(R)` is its instance at ranks
  `1 + 1` and `3 + 1`.  So the parenthetical block argument of the note is not
  needed for the Lean proof; it remains the right explanation to print, but
  the formal dependency is on the prefix code, not on the Steinberg
  commutator through the other block.
-/

namespace GroupApproximation
namespace RankDescent

variable {R : Type*} [Ring R]

/-- **§6, the ring isomorphism** `R ≅ M₂(R)`, for every ring carrying a binary
Leavitt family. -/
noncomputable def ringEquivMatrixTwo (L : LeavittFamily R) :
    R ≃+* Matrix (Fin 2) (Fin 2) R :=
  (L.prefixRingEquiv (leftCombCode 1) (L.leftCombCode_complete 1)).symm

/-- The inverse direction, written out: it is the printed `A ↦ ∑ sᵢ Aᵢⱼ tⱼ`
with the two cylinder words of the comb code in place of `s` and `t`. -/
theorem ringEquivMatrixTwo_symm_apply (L : LeavittFamily R)
    (A : Matrix (Fin 2) (Fin 2) R) :
    (ringEquivMatrixTwo L).symm A =
      ∑ i, ∑ j, L.wordS ((leftCombCode 1).word i) * A i j *
        L.wordT ((leftCombCode 1).word j) := rfl

/-- **§6, the group isomorphism** `EL₂(R) ≅ EL₄(R)`.

This is `LeavittFamily.rankSuccEquiv` at ranks `1 + 1` and `3 + 1`; the note's
block argument is an explanation of why such an isomorphism exists, not the
route taken here. -/
noncomputable def elementaryRankTwoEquivRankFour (L : LeavittFamily R) :
    elementaryGroup (Fin 2) R ≃* elementaryGroup (Fin 4) R :=
  L.rankSuccEquiv 1 3 (by omega) (by omega)

end RankDescent
end GroupApproximation
