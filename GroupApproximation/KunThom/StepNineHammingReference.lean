import GroupApproximation.KunThom.ComponentCountingRelativeFunctorRealization
import Mathlib.Tactic.Group

/-!
# Step 9: a patched bisection against a conjugated patch

The last estimate in Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3,
tex lines 1314--1338) compares the patched bisection `b̂_n` with the conjugate
`u_n â_n u_n⁻¹` of a patched bisection `â_n` by a compressor permutation `u_n`.
This file pulls the comparison back through `u_n`.  The Hamming disagreement of
`b̂` with `u â u⁻¹` has the same size as that of `â` with `u⁻¹ b̂ u`.  On the block
of an object `i` of `â`, the arrow `b_{π i}` transported back through the bridges
realized by `u⁻¹` is a reference arrow for `u⁻¹ b̂ u`.  That transported arrow is
the raw map of the relative functor of Kun--Thom Lemma 4.3 on `b_{π i}`, so estimate
(7) of `RelativeFunctorEstimate` applies to it directly.

* `card_hammingDisagreement_conj_swap`: `#{p ≠ v w v⁻¹} = #{w ≠ v⁻¹ p v}`.
* `BlockEmbedding.realizesOn_sandwich_bridge_inv`: the arrow of block `C` of `β`,
  transported through the bridges realized by `q⁻¹`, realizes `q⁻¹ · β.patch · q`.
* `BlockArrows.card_hammingDisagreement_patch_conj_le_references`: `β.patch`
  differs from `q · α.patch · q⁻¹` by at most the mass off the glued domain of
  `α`, the disagreement of every retained arrow of `α` with a reference arrow for
  `q⁻¹ · β.patch · q`, and the full size of the exceptional blocks.
* `BlockArrows.card_hammingDisagreement_patch_conj_le_sandwich`: the same with the
  transported arrows `b_{π i}` as references.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-- **Swapping a conjugation.**  A permutation `p` disagrees with `v w v⁻¹` on as
many points as `w` disagrees with `v⁻¹ p v`. -/
theorem card_hammingDisagreement_conj_swap (p w v : Equiv.Perm Y) :
    (hammingDisagreement p (v * w * v⁻¹)).card =
      (hammingDisagreement w (v⁻¹ * p * v)).card := by
  rw [hammingDisagreement_eq_support, hammingDisagreement_eq_support]
  have e : (v * w * v⁻¹)⁻¹ * p = v * ((v⁻¹ * p * v)⁻¹ * w)⁻¹ * v⁻¹ := by group
  rw [e, Equiv.Perm.card_support_conj, Equiv.Perm.support_inv]

namespace BlockEmbedding

/-- **Transported arrows are references.**  The arrow of block `C` of `β`,
transported through the bridges realized by `q⁻¹` into block `C'` and into the
image block of `C'` under `α`, realizes `q⁻¹ · β.patch · q`.  For `q = u_n` this is
the raw map of the relative functor of Kun--Thom Lemma 4.3 on the arrow of `C`. -/
theorem realizesOn_sandwich_bridge_inv [Fintype I] (E : BlockEmbedding Y I)
    (α β : BlockArrows E) (q : Equiv.Perm Y) (C C' : I) :
    α.RealizesOn (q⁻¹ * β.patch * q) C'
      (sandwich (E.bridge q⁻¹ C C') (E.bridge q⁻¹ (β.objEquiv C) (α.objEquiv C'))
        (β.arrow C)) := by
  have h := E.realizesOn_sandwich_bridge β α q⁻¹ C C'
  rwa [inv_inv] at h

end BlockEmbedding

namespace BlockArrows

variable {E : BlockEmbedding Y I}

/-- **A patched bisection against a conjugated patch.**  The patched permutation
`β.patch` differs from `q · α.patch · q⁻¹` by at most the mass off the glued
domain of `α`, the disagreement of every retained arrow of `α` with a reference
arrow realizing `q⁻¹ · β.patch · q`, and the full size of the exceptional
blocks. -/
theorem card_hammingDisagreement_patch_conj_le_references [Fintype I] [DecidableEq I]
    (α β : BlockArrows E) (q : Equiv.Perm Y) (good : Finset I)
    (c : ∀ i, FinitePartialBijection (E.model i) (E.model (α.objEquiv i)))
    (hc : ∀ i ∈ good, α.RealizesOn (q⁻¹ * β.patch * q) i (c i)) :
    (hammingDisagreement β.patch (q * α.patch * q⁻¹)).card ≤
      (Finset.univ \ α.domain).card + ∑ i ∈ good, ((α.arrow i).disagreement (c i)).card +
        ∑ i ∈ goodᶜ, Fintype.card (E.model i) := by
  rw [card_hammingDisagreement_conj_swap]
  exact α.card_hammingDisagreement_patch_le_references (q⁻¹ * β.patch * q) good c hc

/-- **Step 9 with transported references.**  On a retained object `i` the
reference arrow is the arrow of `β` at the matched block `π i`, transported back to
the block of `i` through the bridges realized by `q⁻¹`. -/
theorem card_hammingDisagreement_patch_conj_le_sandwich [Fintype I] [DecidableEq I]
    (α β : BlockArrows E) (q : Equiv.Perm Y) (π : I → I) (good : Finset I) :
    (hammingDisagreement β.patch (q * α.patch * q⁻¹)).card ≤
      (Finset.univ \ α.domain).card +
        ∑ i ∈ good, ((α.arrow i).disagreement
          (sandwich (E.bridge q⁻¹ (π i) i) (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i))
            (β.arrow (π i)))).card +
        ∑ i ∈ goodᶜ, Fintype.card (E.model i) :=
  α.card_hammingDisagreement_patch_conj_le_references β q good
    (fun i ↦ sandwich (E.bridge q⁻¹ (π i) i)
      (E.bridge q⁻¹ (β.objEquiv (π i)) (α.objEquiv i)) (β.arrow (π i)))
    (fun i _ ↦ E.realizesOn_sandwich_bridge_inv α β q (π i) i)

end BlockArrows

end BlockPatching
end GroupApproximation
