import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shape: the pinch equations of a chain block

Lane `gl-p04-10`, list helper.  If `d :: (γ ++ [t])` is an `R`-chain and `γ ≠ []`, then `γ` is an
`R`-chain, `R d (head γ)` and `R (last γ) t`.  This turns a contiguous block
`last side_s, gap_s, head side_(s+1)` of the class darts into the three chain hypotheses of the
planar pinch loop (`PinchLoop.faceOf_ne`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace

/-- **The pinch equations of a chain block.**  In an `R`-chain `d :: (γ ++ [t])` with `γ ≠ []`, the
middle block `γ` is an `R`-chain, `d` is related to its head and its last dart to `t`. -/
theorem pinch_chain {α : Type*} {R : α → α → Prop} {d t : α} {γ : List α} (hγ : γ ≠ [])
    (h : (d :: (γ ++ [t])).IsChain R) :
    γ.IsChain R ∧ R d (γ.head hγ) ∧ R (γ.getLast hγ) t := by
  have htail : (γ ++ [t]).IsChain R := h.tail
  refine ⟨htail.left_of_append, ?_, ?_⟩
  · have h1 : ([d] ++ (γ ++ [t])).IsChain R := h
    have h2 := h1.rel_getLast_head_of_append (List.cons_ne_nil d []) (by simp)
    rw [List.head_append_of_ne_nil hγ] at h2
    exact h2
  · exact htail.rel_getLast_head_of_append hγ (List.cons_ne_nil t [])

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace.pinch_chain

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.GapOffFace
