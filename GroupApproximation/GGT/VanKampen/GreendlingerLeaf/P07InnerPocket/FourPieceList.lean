import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

open scoped List

/-!
# Greendlinger leaf P07, inner pocket: cyclic non-interleaving of a binary class

Lane `gl-p07-10` (`lanes/carto-gl-p07.md`), list layer.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`; certifies no printed sentence on its own.
The mathematical proof of the lane is in `FourPieceOrder.lean`.

## Statement

`CyclicNoInterleave A l`: no rotation of `l` has a sublist `[x, y, z, t]` alternating in `A`
(`A, ¬A, A, ¬A` or `¬A, A, ¬A, A`).  `exists_rotate_block`: such a list has a rotation
`U ++ V` with `U` all in `A` and `V` all outside `A`.

## Proof

Split `l = u₁ ++ v ++ u₂ ++ v' ++ r` greedily into maximal blocks `A`, `¬A`, `A`, `¬A`
(`exists_prefix_split`).  Each block after the first is nonempty as soon as something follows it
(`exists_mem_of_heads`).  If `r ≠ []`, the heads of `v, u₂, v', r` alternate.  If `r = []` and
`v' ≠ []`, then `u₁ = []` (else the heads of `u₁, v, u₂, v'` alternate), and rotating by `|v|`
gives `u₂ ++ (v' ++ v)`.  If `r = v' = []`, rotating by `|u₁ ++ v|` gives `(u₂ ++ u₁) ++ v`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece

section Lists

variable {α : Type*}

/-- **Cyclic non-interleaving of a binary class.**  No rotation of `l` contains a sublist of four
entries alternating between `A` and its complement. -/
def CyclicNoInterleave (A : α → Prop) (l : List α) : Prop :=
  ∀ (n : ℕ) (x y z t : α), [x, y, z, t] <+ l.rotate n →
    ¬ (A x ∧ ¬ A y ∧ A z ∧ ¬ A t) ∧ ¬ (¬ A x ∧ A y ∧ ¬ A z ∧ A t)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.CyclicNoInterleave

/-- An alternation `A, ¬A, A, ¬A` in a rotation is impossible. -/
theorem CyclicNoInterleave.not_abab {A : α → Prop} {l l' : List α} (h : CyclicNoInterleave A l)
    {n : ℕ} (hn : l.rotate n = l') (x y z t : α) (hs : [x, y, z, t] <+ l') (hx : A x)
    (hy : ¬ A y) (hz : A z) (ht : ¬ A t) : False :=
  (h n x y z t (by rw [hn]; exact hs)).1 ⟨hx, hy, hz, ht⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.CyclicNoInterleave.not_abab

/-- An alternation `¬A, A, ¬A, A` in a rotation is impossible. -/
theorem CyclicNoInterleave.not_baba {A : α → Prop} {l l' : List α} (h : CyclicNoInterleave A l)
    {n : ℕ} (hn : l.rotate n = l') (x y z t : α) (hs : [x, y, z, t] <+ l') (hx : ¬ A x)
    (hy : A y) (hz : ¬ A z) (ht : A t) : False :=
  (h n x y z t (by rw [hn]; exact hs)).2 ⟨hx, hy, hz, ht⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.CyclicNoInterleave.not_baba

/-- Four entries of four consecutive blocks form a sublist. -/
theorem sublist_four {x y z t : α} {l₁ l₂ l₃ l₄ : List α} (h₁ : x ∈ l₁) (h₂ : y ∈ l₂)
    (h₃ : z ∈ l₃) (h₄ : t ∈ l₄) : [x, y, z, t] <+ l₁ ++ (l₂ ++ (l₃ ++ l₄)) :=
  (List.singleton_sublist.mpr h₁).append ((List.singleton_sublist.mpr h₂).append
    ((List.singleton_sublist.mpr h₃).append (List.singleton_sublist.mpr h₄)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.sublist_four

/-- **Greedy maximal prefix.**  Every list is a prefix of entries in `A` followed by a rest whose
head, if any, is not in `A`. -/
theorem exists_prefix_split (A : α → Prop) :
    ∀ l : List α, ∃ u r : List α, l = u ++ r ∧ (∀ x ∈ u, A x) ∧ ∀ y s, r = y :: s → ¬ A y
  | [] => ⟨[], [], rfl, fun _ hx => by simp at hx, fun _ _ h => nomatch h⟩
  | x :: l => by
    by_cases hx : A x
    · obtain ⟨u, r, hl, hu, hr⟩ := exists_prefix_split A l
      refine ⟨x :: u, r, by rw [hl, List.cons_append], ?_, hr⟩
      intro z hz
      rcases List.mem_cons.mp hz with hzx | hz
      · rw [hzx]
        exact hx
      · exact hu z hz
    · refine ⟨[], x :: l, rfl, fun _ hz => by simp at hz, ?_⟩
      intro y s h
      rw [← (List.cons_eq_cons.mp h).1]
      exact hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.exists_prefix_split

/-- **A block before a clashing head is nonempty.**  If the head of `u ++ r` satisfies `B`, the
head of the nonempty `r` satisfies `C`, and `B`, `C` are incompatible, then `u` is nonempty. -/
theorem exists_mem_of_heads {B C : α → Prop} (hBC : ∀ z, B z → C z → False) {u r : List α}
    (hwhole : ∀ z t, u ++ r = z :: t → B z) (hrest : ∀ z t, r = z :: t → C z) (hne : r ≠ []) :
    ∃ x, x ∈ u := by
  cases u with
  | nil =>
    obtain ⟨z, t, hzt⟩ := List.exists_cons_of_ne_nil hne
    exact (hBC z (hwhole z t hzt) (hrest z t hzt)).elim
  | cons x u => exact ⟨x, List.mem_cons_self⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.exists_mem_of_heads

/-- **A cyclically non-interleaving class is a cyclic block.**  Some rotation of `l` is `U ++ V`
with `U` inside `A` and `V` outside `A`. -/
theorem exists_rotate_block {A : α → Prop} {l : List α} (h : CyclicNoInterleave A l) :
    ∃ (n : ℕ) (U V : List α), l.rotate n = U ++ V ∧ (∀ x ∈ U, A x) ∧ ∀ x ∈ V, ¬ A x := by
  obtain ⟨u₁, r₁, rfl, hu₁, hr₁⟩ := exists_prefix_split A l
  obtain ⟨v, r₂, rfl, hv, hr₂⟩ := exists_prefix_split (fun x => ¬ A x) r₁
  obtain ⟨u₂, r₃, rfl, hu₂, hr₃⟩ := exists_prefix_split A r₂
  obtain ⟨v', r₄, rfl, hv', hr₄⟩ := exists_prefix_split (fun x => ¬ A x) r₃
  cases r₄ with
  | cons y s =>
    exfalso
    obtain ⟨v'₀, hv'₀⟩ := exists_mem_of_heads (B := fun x => ¬ A x) (C := fun x => ¬ ¬ A x)
      (fun _ b c => c b) hr₃ hr₄ (List.cons_ne_nil y s)
    obtain ⟨u₂₀, hu₂₀⟩ := exists_mem_of_heads (B := fun x => ¬ ¬ A x) (C := fun x => ¬ A x)
      (fun _ b c => b c) hr₂ hr₃ (by simp)
    obtain ⟨v₀, hv₀⟩ := exists_mem_of_heads (B := fun x => ¬ A x) (C := fun x => ¬ ¬ A x)
      (fun _ b c => c b) hr₁ hr₂ (by simp)
    have hs : [v₀, u₂₀, v'₀, y] <+ u₁ ++ (v ++ (u₂ ++ (v' ++ y :: s))) :=
      (sublist_four hv₀ hu₂₀ hv'₀ List.mem_cons_self).trans (List.sublist_append_right u₁ _)
    exact h.not_baba (List.rotate_zero _) v₀ u₂₀ v'₀ y hs (hv v₀ hv₀) (hu₂ u₂₀ hu₂₀)
      (hv' v'₀ hv'₀) (Classical.not_not.mp (hr₄ y s rfl))
  | nil =>
    cases v' with
    | nil =>
      refine ⟨(u₁ ++ v).length, u₂ ++ u₁, v, ?_, ?_, hv⟩
      · have e : u₁ ++ (v ++ (u₂ ++ ([] ++ []))) = (u₁ ++ v) ++ u₂ := by
          simp only [List.append_nil, List.append_assoc]
        rw [e, List.rotate_append_length_eq, List.append_assoc]
      · intro x hx
        exact (List.mem_append.mp hx).elim (hu₂ x) (hu₁ x)
    | cons v₀ v's =>
      obtain ⟨u₂₀, hu₂₀⟩ := exists_mem_of_heads (B := fun x => ¬ ¬ A x) (C := fun x => ¬ A x)
        (fun _ b c => b c) hr₂ hr₃ (by simp)
      obtain ⟨v₁, hv₁⟩ := exists_mem_of_heads (B := fun x => ¬ A x) (C := fun x => ¬ ¬ A x)
        (fun _ b c => c b) hr₁ hr₂ (by simp)
      cases u₁ with
      | cons x₀ u₁' =>
        exfalso
        have hs : [x₀, v₁, u₂₀, v₀] <+ (x₀ :: u₁') ++ (v ++ (u₂ ++ ((v₀ :: v's) ++ []))) :=
          sublist_four List.mem_cons_self hv₁ hu₂₀ (by simp)
        exact h.not_abab (List.rotate_zero _) x₀ v₁ u₂₀ v₀ hs (hu₁ x₀ List.mem_cons_self)
          (hv v₁ hv₁) (hu₂ u₂₀ hu₂₀) (hv' v₀ List.mem_cons_self)
      | nil =>
        refine ⟨v.length, u₂, (v₀ :: v's) ++ v, ?_, hu₂, ?_⟩
        · have e : ([] : List α) ++ (v ++ (u₂ ++ ((v₀ :: v's) ++ []))) =
              v ++ (u₂ ++ (v₀ :: v's)) := by
            simp only [List.nil_append, List.append_nil]
          rw [e, List.rotate_append_length_eq, List.append_assoc]
        · intro x hx
          exact (List.mem_append.mp hx).elim (hv' x) (hv x)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.exists_rotate_block

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece
