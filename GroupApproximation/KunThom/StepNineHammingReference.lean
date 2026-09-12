import GroupApproximation.KunThom.ComponentCountingRelativeFunctorRealization
import Mathlib.Tactic.Group

/-!
# Step 9: a patched bisection against a conjugated patch

The last estimate in Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222v3,
tex lines 1314--1338) compares the patched bisection `b̂_n` with the conjugate
`u_n â_n u_n⁻¹` of a patched bisection `â_n` by a compressor permutation `u_n`.
This file pulls the comparison back through `u_n`.  The Hamming disagreement of
`b̂` with `u â u⁻¹` has the same size as that of `â` with `u⁻¹ b̂ u`, and on
the block of an object `i` of `â` the arrow `b_{π i}`, transported back through
the two bridges realized by `u`, is a reference arrow for `u⁻¹ b̂ u`.

* `card_hammingDisagreement_conj_swap`: `#{p ≠ v w v⁻¹} = #{w ≠ v⁻¹ p v}`.
* `BlockEmbedding.transportArrow E q β C C' D`: the arrow of block `C` of `β`,
  entered from block `C'` through the bridge realized by `q` and left into block
  `D` through the bridge realized by `q⁻¹`.
* `BlockEmbedding.realizesOn_transportArrow`: the transported arrow realizes
  `q⁻¹ · β.patch · q` on its source.
* `BlockArrows.card_hammingDisagreement_patch_conj_le_references`: `β.patch`
  differs from `q · α.patch · q⁻¹` by at most the mass off the glued domain of
  `α`, the disagreement of every retained arrow of `α` with a reference arrow for
  `q⁻¹ · β.patch · q`, and the full size of the exceptional blocks.
* `BlockArrows.card_hammingDisagreement_patch_conj_le_transport`: the same with
  the transported arrows `b_{π i}` as references.
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

/-- The arrow of block `C` of a block permutation `β`, transported back through
the bridge realized by `q` from block `C'` into `C`, and the bridge realized by
`q⁻¹` from the image block of `C` into block `D`. -/
noncomputable def transportArrow (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (β : BlockArrows E) (C C' D : I) : FinitePartialBijection (E.model C') (E.model D) :=
  ((E.bridge q C' C).trans (β.arrow C)).trans (E.bridge q⁻¹ (β.objEquiv C) D)

/-- The transported arrow is `q⁻¹ · β.patch · q` read through the embeddings. -/
theorem embed_transportArrow_apply [Fintype I] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (β : BlockArrows E) (C C' D : I) (x : E.model C')
    (hx : x ∈ (E.transportArrow q β C C' D).source) :
    E.embed D ((E.transportArrow q β C C' D).apply x hx) =
      (q⁻¹ * β.patch * q) (E.embed C' x) := by
  obtain ⟨h₁, h₂⟩ := (mem_trans_source ((E.bridge q C' C).trans (β.arrow C))
    (E.bridge q⁻¹ (β.objEquiv C) D) x).mp hx
  obtain ⟨h₃, h₄⟩ := (mem_trans_source (E.bridge q C' C) (β.arrow C) x).mp h₁
  have hval : (E.transportArrow q β C C' D).apply x hx =
      (E.bridge q⁻¹ (β.objEquiv C) D).apply
        ((β.arrow C).apply ((E.bridge q C' C).apply x h₃) h₄) h₂ :=
    rfl
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hval, E.embed_bridge_apply,
    ← β.patch_embed C _ h₄, E.embed_bridge_apply]

/-- **Transported arrows are references.**  For a block permutation `α` whose
object map sends `C'` to the target block, the arrow of block `C` of `β`
transported to `C'` realizes `q⁻¹ · β.patch · q` on its source. -/
theorem realizesOn_transportArrow [Fintype I] (E : BlockEmbedding Y I)
    (α β : BlockArrows E) (q : Equiv.Perm Y) (C C' : I) :
    α.RealizesOn (q⁻¹ * β.patch * q) C' (E.transportArrow q β C C' (α.objEquiv C')) :=
  fun x hx ↦ E.embed_transportArrow_apply q β C C' (α.objEquiv C') x hx

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
reference arrow is the arrow of `β` at the matched block `π i`, transported back
to the block of `i` through the bridges realized by `q`. -/
theorem card_hammingDisagreement_patch_conj_le_transport [Fintype I] [DecidableEq I]
    (α β : BlockArrows E) (q : Equiv.Perm Y) (π : I → I) (good : Finset I) :
    (hammingDisagreement β.patch (q * α.patch * q⁻¹)).card ≤
      (Finset.univ \ α.domain).card +
        ∑ i ∈ good, ((α.arrow i).disagreement
          (E.transportArrow q β (π i) i (α.objEquiv i))).card +
        ∑ i ∈ goodᶜ, Fintype.card (E.model i) :=
  α.card_hammingDisagreement_patch_conj_le_references β q good
    (fun i ↦ E.transportArrow q β (π i) i (α.objEquiv i))
    (fun i _ ↦ E.realizesOn_transportArrow α β q (π i) i)

end BlockArrows

end BlockPatching
end GroupApproximation
