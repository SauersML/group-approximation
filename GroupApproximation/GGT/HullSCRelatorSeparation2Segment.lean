import GroupApproximation.GGT.HullSCRelatorSeparation2Join

/-!
# A segment of the run is a run

The window clause of `GGT/HullSCRelatorSeparation2Window.lean` speaks about
`a_s^n · listVal (blockWord … (post.take r))` -- a product of consecutive block
letters read as a run in its own right.  The polygon speaks about
`(vertex 1 q t)⁻¹ * vertex 1 q t'` -- what the path between two positions of a
side spells.  This module is the translation, and it is three list facts.

* `exists_blockWord_drop` -- dropping letters from a run leaves a run, of the
  dropped exponents.  The starting index is existential: `blockWord` flips it at
  each letter, so which index the tail starts at depends on the parity of the
  drop, and nothing downstream needs to know which.
* `blockWord_take` -- taking letters from a run leaves a run, of the taken
  exponents, at the same starting index.
* `exists_listVal_run_segment` -- so what the path between two positions of the
  run spells is what a run of the corresponding sublist spells.

With it, an alternating product of block letters between two component starts is
literally an instance of the expression the design's window clause forbids, and
the two vocabularies meet.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Segment

variable {G : Type u} [Group G]

/-- **A tail of a run is a run.** -/
theorem exists_blockWord_drop (h₀ h₁ : G) :
    ∀ (t : ℕ) (s : Bool) (ms : List ℕ),
      ∃ s' : Bool,
        (blockWord h₀ h₁ s ms).drop t = blockWord h₀ h₁ s' (ms.drop t) := by
  intro t
  induction t with
  | zero =>
      intro s ms
      exact ⟨s, by rw [List.drop_zero, List.drop_zero]⟩
  | succ t ih =>
      intro s ms
      cases ms with
      | nil =>
          refine ⟨s, ?_⟩
          rw [blockWord_nil, List.drop_nil, List.drop_nil, blockWord_nil]
      | cons m ms' =>
          obtain ⟨s'', hs''⟩ := ih (!s) ms'
          refine ⟨s'', ?_⟩
          rw [blockWord_cons, List.drop_succ_cons, List.drop_succ_cons, hs'']

/-- **An initial part of a run is a run.** -/
theorem blockWord_take (h₀ h₁ : G) :
    ∀ (k : ℕ) (s : Bool) (ms : List ℕ),
      (blockWord h₀ h₁ s ms).take k = blockWord h₀ h₁ s (ms.take k) := by
  intro k
  induction k with
  | zero =>
      intro s ms
      rw [List.take_zero, List.take_zero, blockWord_nil]
  | succ k ih =>
      intro s ms
      cases ms with
      | nil => rw [blockWord_nil, List.take_nil, List.take_nil, blockWord_nil]
      | cons m ms' =>
          rw [blockWord_cons, List.take_succ_cons, List.take_succ_cons,
            blockWord_cons, ih]

/-- **What the path between two positions of the run spells is what the
corresponding run of exponents spells.** -/
theorem exists_listVal_run_segment (h₀ h₁ : G) (s : Bool) (ms : List ℕ)
    {t k : ℕ} (htk : t + k ≤ ms.length) :
    ∃ s' : Bool,
      (GGT.OsinComponents.vertex (1 : G) (blockWord h₀ h₁ s ms) t)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) (blockWord h₀ h₁ s ms) (t + k)
        = GGT.RelLetter.listVal (blockWord h₀ h₁ s' ((ms.drop t).take k)) := by
  have hlen : (blockWord h₀ h₁ s ms).length = ms.length :=
    length_blockWord h₀ h₁ s ms
  have hsplit : (blockWord h₀ h₁ s ms).take (t + k)
      = (blockWord h₀ h₁ s ms).take t
        ++ ((blockWord h₀ h₁ s ms).drop t).take k := by
    rw [List.take_drop]
    conv_lhs => rw [← List.take_append_drop t ((blockWord h₀ h₁ s ms).take (t + k))]
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right t k)]
  obtain ⟨s', hs'⟩ := exists_blockWord_drop h₀ h₁ t s ms
  have ht : t ≤ (blockWord h₀ h₁ s ms).length := by omega
  have htk' : t + k ≤ (blockWord h₀ h₁ s ms).length := by omega
  refine ⟨s', ?_⟩
  rw [vertex_eq_listVal_take 1 (blockWord h₀ h₁ s ms) ht,
    vertex_eq_listVal_take 1 (blockWord h₀ h₁ s ms) htk',
    one_mul, one_mul, hsplit, RelWord.listVal_append, ← mul_assoc,
    inv_mul_cancel, one_mul, hs', blockWord_take]

end Segment

end HullSC
end GroupApproximation
