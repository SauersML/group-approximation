import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Counting lemmas for the crossing parity

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-20.

## Route

* `regionMoveLoose_countP_add`: `#p + #q = 2 · #(p ∧ q) + #(p ≠ q)` over a list.
* `regionMoveLoose_countP_comm`: for two lists without repetition,
  `#{a ∈ l₁ | a ∈ l₂} = #{a ∈ l₂ | a ∈ l₁}`.
* `regionMoveLoose_even_countP_bne`: along `a, a+1, …, a+n` a Boolean sequence changes value an even
  number of times exactly when its two ends agree (telescoping).
* `regionMoveLoose_countP_attach_next`: counting through the cyclic successor `List.next` on a
  list without repetition is counting on the list itself (`next` permutes the list).
* `regionMoveLoose_countP_eq_one`: a predicate true at exactly one entry is counted once.

## Truth check

Proved lemmas about finite lists.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

open scoped Classical

/-- **Two Boolean indicators**: `[b₁] + [b₂] = 2 [b₁ ∧ b₂] + [b₁ ≠ b₂]`. -/
theorem regionMoveLoose_ite_bool (b₁ b₂ : Bool) :
    ((if b₁ = true then 1 else 0) + (if b₂ = true then 1 else 0) : ℕ) =
      2 * (if (b₁ && b₂) = true then 1 else 0) + (if (b₁ != b₂) = true then 1 else 0) := by
  cases b₁ <;> cases b₂ <;> decide

/-- **Counting two predicates**: `#p + #q = 2 · #(p ∧ q) + #(p ≠ q)`. -/
theorem regionMoveLoose_countP_add {β : Type*} (p q : β → Bool) (l : List β) :
    l.countP p + l.countP q =
      2 * l.countP (fun a => p a && q a) + l.countP (fun a => p a != q a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have h := regionMoveLoose_ite_bool (p a) (q a)
    omega

/-- **Counting common entries both ways**: for two lists without repetition, the entries of `l₁`
lying in `l₂` are as many as the entries of `l₂` lying in `l₁`. -/
theorem regionMoveLoose_countP_comm {β : Type*} {l₁ l₂ : List β} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (p₁ p₂ : β → Bool) (hp₁ : ∀ a, p₁ a = true ↔ a ∈ l₂)
    (hp₂ : ∀ a, p₂ a = true ↔ a ∈ l₁) : l₁.countP p₁ = l₂.countP p₂ := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (h₁.filter p₁) (h₂.filter p₂)]
  intro a
  rw [List.mem_filter, List.mem_filter, hp₁, hp₂]
  exact and_comm

/-- **Telescoping mod two**: along `a, …, a + n`, a Boolean sequence changes value an even number of
times exactly when `g a = g (a + n)`. -/
theorem regionMoveLoose_even_countP_bne (g : ℕ → Bool) (a n : ℕ) :
    Even ((List.range' a n).countP (fun i => g i != g (i + 1))) ↔ g a = g (a + n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    simp only [List.range'_succ, List.countP_cons]
    rw [show a + (n + 1) = a + 1 + n by omega]
    have ih' := ih (a + 1)
    rw [Nat.even_iff] at ih' ⊢
    generalize (List.range' (a + 1) n).countP (fun i => g i != g (i + 1)) = m at ih' ⊢
    generalize g (a + 1 + n) = b₂ at ih' ⊢
    generalize g (a + 1) = b₁ at ih' ⊢
    generalize g a = b₀
    cases b₀ <;> cases b₁ <;> cases b₂ <;> simp at ih' ⊢ <;> omega

/-- **Counting through the cyclic successor**: on a list without repetition, `List.next` permutes
the entries, so a count through it is a count on the list. -/
theorem regionMoveLoose_countP_attach_next {β : Type*} {l : List β} (hl : l.Nodup)
    (p : β → Bool) : l.attach.countP (fun q => p (l.next q.1 q.2)) = l.countP p := by
  have e1 : l.attach.countP (fun q => p (l.next q.1 q.2)) =
      (l.attach.map (fun q => l.next q.1 q.2)).countP p := by
    rw [List.countP_map]
    try rfl
  have e2 : l.pmap l.next (fun _ h => h) = l.attach.map (fun q => l.next q.1 q.2) := by
    rw [List.pmap_eq_map_attach]
  rw [e1, ← e2, List.pmap_next_eq_rotate_one hl, (List.rotate_perm l 1).countP_eq]

/-- **A predicate true at exactly one entry is counted once.** -/
theorem regionMoveLoose_countP_eq_one {β : Type*} {l : List β} (hl : l.Nodup) {a : β}
    (ha : a ∈ l) (p : β → Bool) (hp : ∀ b ∈ l, p b = true ↔ b = a) : l.countP p = 1 := by
  rw [List.countP_eq_length_filter]
  have hperm : List.Perm (l.filter p) [a] := by
    rw [List.perm_ext_iff_of_nodup (hl.filter p) (List.nodup_singleton a)]
    intro b
    rw [List.mem_filter, List.mem_singleton]
    constructor
    · rintro ⟨hb, hpb⟩
      exact (hp b hb).mp hpb
    · intro h
      rw [h]
      exact ⟨ha, (hp a ha).mpr rfl⟩
  exact hperm.length_eq

/-- **Membership in an involutive image.** -/
theorem regionMoveLoose_mem_map_involutive {β : Type*} {f : β → β} (hf : Function.Involutive f)
    {l : List β} {a : β} : a ∈ l.map f ↔ f a ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hf b]
    exact hb
  · intro h
    exact ⟨f a, h, hf a⟩

/-- **Two decisions differ exactly when the propositions do.** -/
theorem regionMoveLoose_bne_true_iff {A B : Prop} [Decidable A] [Decidable B] :
    (decide A != decide B) = true ↔ ¬(A ↔ B) := by
  by_cases hA : A <;> by_cases hB : B
  · rw [decide_eq_true hA, decide_eq_true hB]
    exact iff_of_false (by decide) (fun h => h (iff_of_true hA hB))
  · rw [decide_eq_true hA, decide_eq_false hB]
    exact iff_of_true rfl (fun h => hB (h.mp hA))
  · rw [decide_eq_false hA, decide_eq_true hB]
    exact iff_of_true rfl (fun h => hA (h.mpr hB))
  · rw [decide_eq_false hA, decide_eq_false hB]
    exact iff_of_false (by decide) (fun h => h (iff_of_false hA hB))

/-- **Boundary indicators against inside indicators**: if `p ↔ r ∧ ¬s` and `q ↔ s ∧ ¬r`, then
`[p] ≠ [q]` exactly when `[r] ≠ [s]`. -/
theorem regionMoveLoose_bne_decide {p q r s : Prop} [Decidable p] [Decidable q] [Decidable r]
    [Decidable s] (h1 : p ↔ r ∧ ¬s) (h2 : q ↔ s ∧ ¬r) :
    (decide p != decide q) = (decide r != decide s) := by
  by_cases hr : r <;> by_cases hs : s
  · rw [decide_eq_false (fun h => (h1.mp h).2 hs), decide_eq_false (fun h => (h2.mp h).2 hr),
      decide_eq_true hr, decide_eq_true hs]
  · rw [decide_eq_true (h1.mpr ⟨hr, hs⟩), decide_eq_false (fun h => hs (h2.mp h).1),
      decide_eq_true hr, decide_eq_false hs]
  · rw [decide_eq_false (fun h => hr (h1.mp h).1), decide_eq_true (h2.mpr ⟨hs, hr⟩),
      decide_eq_false hr, decide_eq_true hs]
  · rw [decide_eq_false (fun h => hr (h1.mp h).1), decide_eq_false (fun h => hs (h2.mp h).1),
      decide_eq_false hr, decide_eq_false hs]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_ite_bool
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_countP_add
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_countP_comm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_even_countP_bne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_countP_attach_next
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_countP_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_mem_map_involutive
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_bne_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLoose_bne_decide
