import GroupApproximation.GGT.HullSCRelatorSeparation2Segment
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyBlock

/-!
# Segments of a rotation are prefixes of a further rotation

The same-side parser sees a segment `[i,j)` of a rotated relator.  Cyclic-word
bookkeeping is substantially cleaner after moving its initial vertex to zero:
the segment is exactly the prefix of length `j-i` of the further rotation by
`c+i`.  These lemmas perform that normalization without assuming that the
segment stays on one side of the original rotation seam.
-/

namespace GroupApproximation
namespace HullSC

universe u v

section Lists

/-- A segment of a rotation is a prefix of the rotation based at the segment's
first position. -/
theorem drop_take_rotate_eq_take_rotate {α : Type v} (l : List α)
    {c i k : ℕ} (hik : i + k ≤ l.length) :
    ((l.rotate c).drop i).take k = (l.rotate (c + i)).take k := by
  apply List.ext_getElem?
  intro q
  rcases Nat.lt_or_ge q k with hq | hq
  · rw [List.getElem?_take_of_lt hq, List.getElem?_drop,
      List.getElem?_rotate (by omega), List.getElem?_take_of_lt hq,
      List.getElem?_rotate (by omega)]
    rw [show q + (c + i) = i + q + c by omega]
  · have hleft : (((l.rotate c).drop i).take k)[q]? = none := by
      apply List.getElem?_eq_none
      simp only [List.length_take, List.length_drop, List.length_rotate]
      omega
    have hright : ((l.rotate (c + i)).take k)[q]? = none := by
      apply List.getElem?_eq_none
      simp only [List.length_take, List.length_rotate]
      omega
    rw [hleft, hright]

/-- Rotating a word consisting of one distinguished base letter followed by a
run to the `q`-th run letter exposes the two run pieces on the two sides of the
base seam. -/
theorem rotate_cons_eq_drop_append_cons_append_take {α : Type v}
    (base : α) (run : List α) {q : ℕ} (hq : q ≤ run.length) :
    (base :: run).rotate (q + 1) =
      run.drop q ++ base :: run.take q := by
  rw [List.rotate_eq_drop_append_take (by simp; omega)]
  simp only [List.drop_succ_cons, List.take_succ_cons]

/-- The same expansion in the `relatorWord₂ [base]` notation used by the exact
design. -/
theorem rotate_relatorWord₂_singleton_at_block
    {G : Type u} [Group G] (base h₀ h₁ : G) (ms : List ℕ)
    {q : ℕ} (hq : q ≤ ms.length) :
    (relatorWord₂ [base] h₀ h₁ ms).rotate (q + 1) =
      (blockWord h₀ h₁ false ms).drop q ++
        GGT.RelLetter.base base ::
          (blockWord h₀ h₁ false ms).take q := by
  change (GGT.RelLetter.base base :: blockWord h₀ h₁ false ms).rotate (q + 1)
      = _
  apply rotate_cons_eq_drop_append_cons_append_take
  simpa only [length_blockWord] using hq

/-- After exposing the `q`-th block as the first letter, peeling that anchor
leaves the remaining run suffix, the base letter, and the run prefix, in that
order. -/
theorem take_succ_rotate_relatorWord₂_singleton_at_block
    {G : Type u} [Group G] (base h₀ h₁ : G) (ms : List ℕ)
    {q k : ℕ} (hq : q < ms.length) {x : GGT.RelLetter G Bool}
    (hx : (blockWord h₀ h₁ false ms)[q]? = some x) :
    ((relatorWord₂ [base] h₀ h₁ ms).rotate (q + 1)).take (k + 1) =
      x ::
        ((blockWord h₀ h₁ false ms).drop (q + 1) ++
          GGT.RelLetter.base base ::
            (blockWord h₀ h₁ false ms).take q).take k := by
  rw [rotate_relatorWord₂_singleton_at_block base h₀ h₁ ms (le_of_lt hq)]
  have hqB : q < (blockWord h₀ h₁ false ms).length := by
    simpa only [length_blockWord] using hq
  rw [List.drop_eq_getElem_cons hqB]
  rw [getElem_eq_of_getElem? hqB hx]
  exact List.take_succ_cons

/-- The word after the peeled anchor splits canonically at the base seam.  The
first summand is the remaining suffix of the run; the second is a (possibly
empty) prefix beginning with the base letter. -/
theorem peeled_cyclic_tail_split
    {G : Type u} [Group G] (base h₀ h₁ : G) (ms : List ℕ)
    (q k : ℕ) :
    ((blockWord h₀ h₁ false ms).drop (q + 1) ++
      GGT.RelLetter.base base ::
        (blockWord h₀ h₁ false ms).take q).take k =
      ((blockWord h₀ h₁ false ms).drop (q + 1)).take k ++
        (GGT.RelLetter.base base ::
          (blockWord h₀ h₁ false ms).take q).take
            (k - ((blockWord h₀ h₁ false ms).drop (q + 1)).length) := by
  exact List.take_append

/-- In exponent-list coordinates, the suffix in the preceding split is again
an alternating block word, while the prefix on the far side of the seam keeps
the original initial index. -/
theorem exists_peeled_cyclic_tail_block_split
    {G : Type u} [Group G] (base h₀ h₁ : G) (ms : List ℕ)
    (q k : ℕ) :
    ∃ b : Bool,
      ((blockWord h₀ h₁ false ms).drop (q + 1) ++
        GGT.RelLetter.base base ::
          (blockWord h₀ h₁ false ms).take q).take k =
        blockWord h₀ h₁ b ((ms.drop (q + 1)).take k) ++
          (GGT.RelLetter.base base ::
            blockWord h₀ h₁ false (ms.take q)).take
              (k - (ms.length - (q + 1))) := by
  obtain ⟨b, hb⟩ := exists_blockWord_drop h₀ h₁ (q + 1) false ms
  refine ⟨b, ?_⟩
  rw [peeled_cyclic_tail_split, hb, blockWord_take, blockWord_take,
    length_blockWord, List.length_drop]

end Lists

section Span

variable {G : Type u} [Group G] {Λ : Type v}

/-- The element spelt by a forward span of a rotation is the value of the
corresponding prefix based at its first cyclic position. -/
theorem span_rotate_eq_listVal_take_rotate
    (l : List (GGT.RelLetter G Λ)) {c i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ l.length) :
    (GGT.OsinComponents.vertex (1 : G) (l.rotate c) i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) (l.rotate c) j =
      GGT.RelLetter.listVal ((l.rotate (c + i)).take (j - i)) := by
  have hseg := GGT.OsinComponents.listVal_segment (l.rotate c) (1 : G) hij
  rw [← hseg, ← mul_assoc, inv_mul_cancel, one_mul]
  congr 1
  have hik : i + (j - i) ≤ l.length := by omega
  exact drop_take_rotate_eq_take_rotate l hik

end Span

end HullSC
end GroupApproximation
