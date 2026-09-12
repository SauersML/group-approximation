import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBridges
import GroupApproximation.Matching.PartialBijectionSandwich

/-!
# Transported arrows realize the conjugated patched permutation

In the endgame of Kun and Thom's proof of Theorem 4.1 (arXiv:2608.06222), a
patched bisection `â` of the cluster groupoid is conjugated by a compressor
permutation `u`.  On the matched component `Q_{π i}`, the reference arrow is the
arrow `a_i : Q_i ⇢ Q_{ā i}` transported through the two bridges realized by `u`.
This file proves that the transported arrow realizes `u · patch(â) · u⁻¹` exactly
on its source, in the form consumed by
`BlockPatching.BlockArrows.card_hammingDisagreement_patch_le_references`.
-/

namespace GroupApproximation
namespace BlockPatching
namespace BlockEmbedding

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-- The inverse bridge is `q⁻¹` read through the two embeddings. -/
theorem embed_bridge_symm_apply (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (z : E.model D) (hz : z ∈ (E.bridge q C D).symm.source) :
    E.embed C ((E.bridge q C D).symm.apply z hz) = q⁻¹ (E.embed D z) :=
  E.embed_bridgeApplyInv q C D z hz

/-- **Transported arrows realize the conjugated patch.**  The arrow of block `C`
of a block permutation `β`, transported through the bridges realized by `q` from
`C` to `C'` and from `β.objEquiv C` to `D`, is `q · β.patch · q⁻¹` read through
the embeddings. -/
theorem embed_sandwich_bridge_apply [Fintype I] (E : BlockEmbedding Y I)
    (β : BlockArrows E) (q : Equiv.Perm Y) (C C' D : I) (x : E.model C')
    (hx : x ∈ (sandwich (E.bridge q C C') (E.bridge q (β.objEquiv C) D)
      (β.arrow C)).source) :
    E.embed D ((sandwich (E.bridge q C C') (E.bridge q (β.objEquiv C) D)
        (β.arrow C)).apply x hx) =
      (q * β.patch * q⁻¹) (E.embed C' x) := by
  obtain ⟨h₁, h₂⟩ := (mem_trans_source ((E.bridge q C C').symm.trans (β.arrow C))
    (E.bridge q (β.objEquiv C) D) x).mp hx
  obtain ⟨h₃, h₄⟩ := (mem_trans_source (E.bridge q C C').symm (β.arrow C) x).mp h₁
  have hval : (sandwich (E.bridge q C C') (E.bridge q (β.objEquiv C) D)
      (β.arrow C)).apply x hx =
        (E.bridge q (β.objEquiv C) D).apply
          ((β.arrow C).apply ((E.bridge q C C').symm.apply x h₃) h₄) h₂ :=
    rfl
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hval, E.embed_bridge_apply,
    ← β.patch_embed C _ h₄, E.embed_bridge_symm_apply]

/-- The transported arrows are reference arrows for the conjugated patch, in the
sense of `BlockArrows.RealizesOn`, for any block permutation `β'` whose object
map sends `C'` to the image block. -/
theorem realizesOn_sandwich_bridge [Fintype I] (E : BlockEmbedding Y I)
    (β β' : BlockArrows E) (q : Equiv.Perm Y) (C C' : I) :
    β'.RealizesOn (q * β.patch * q⁻¹) C'
      (sandwich (E.bridge q C C') (E.bridge q (β.objEquiv C) (β'.objEquiv C'))
        (β.arrow C)) :=
  fun x hx ↦ E.embed_sandwich_bridge_apply β q C C' (β'.objEquiv C') x hx

end BlockEmbedding
end BlockPatching
end GroupApproximation
