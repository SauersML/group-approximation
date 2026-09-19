import GroupApproximation.Kourovka1759.PC

/-!
# Identities among class transpositions

Research node: `class-transposition-presentation-has-central-kernel` (Kourovka 17.61 lane).

The swaps `swap A B h` of disjoint boxes (`GroupApproximation.Kourovka1759`) satisfy the three
families of relations of the transposition presentation:
* `swap_mul_self`: squares;
* `conj_swap`: conjugation by a permutation that is canonical on both boxes;
* `swap_split`: splitting both boxes into corresponding `k`-children.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- A permutation that maps `A` onto `B` and `B` onto `A` canonically and fixes the rest is the
swap of `A` and `B`. -/
theorem swap_eq_of (g : Perm ℤ) {A B : Box} (h : A.Disj B) (h1 : CanonOn g A B)
    (h2 : CanonOn g B A) (h3 : ∀ n, ¬ A.Mem n → ¬ B.Mem n → g n = n) : g = swap A B h := by
  refine Equiv.ext fun n => ?_
  by_cases ha : A.Mem n
  · exact h1.agree (swap_canon h) ha
  by_cases hb : B.Mem n
  · exact h2.agree (swap_canon' h) hb
  rw [h3 n ha hb, swap_fix h ha hb]

theorem swap_comm {A B : Box} (h : A.Disj B) : swap A B h = swap B A h.symm :=
  swap_eq_of _ h.symm (swap_canon' h) (swap_canon h) fun _ hb ha => swap_fix h ha hb

theorem swap_mul_self {A B : Box} (h : A.Disj B) : swap A B h * swap A B h = 1 := by
  refine Equiv.ext fun n => ?_
  rw [Perm.mul_apply, Perm.one_apply, swap_apply, swap_apply]
  exact swapFun_invol h n

theorem swap_inv {A B : Box} (h : A.Disj B) : (swap A B h)⁻¹ = swap A B h :=
  inv_eq_of_mul_eq_one_right (swap_mul_self h)

/-- Conjugating a swap by a permutation that is canonical on both boxes gives the swap of the
image boxes. -/
theorem conj_swap {c : Perm ℤ} {A B A' B' : Box} (h : A.Disj B) (h' : A'.Disj B')
    (hA : CanonOn c A A') (hB : CanonOn c B B') : c * swap A B h * c⁻¹ = swap A' B' h' := by
  refine swap_eq_of _ h' ?_ ?_ ?_
  · have := (hA.inv.comp (swap_canon h)).comp hB
    simpa only [mul_assoc] using this
  · have := (hB.inv.comp (swap_canon' h)).comp hA
    simpa only [mul_assoc] using this
  · intro n ha hb
    have ha' : ¬ A.Mem (c⁻¹ n) := fun hm => ha (by simpa using hA.mem hm)
    have hb' : ¬ B.Mem (c⁻¹ n) := fun hm => hb (by simpa using hB.mem hm)
    rw [Perm.mul_apply, Perm.mul_apply, swap_fix h ha' hb', Perm.apply_inv_self]

/-- `n` lies in the `j`-th pair of `k`-children of `A, B`. -/
def InKid (A B : Box) (k : ℕ) (j : Fin k) (n : ℤ) : Prop :=
  (place A (child k j)).Mem n ∨ (place B (child k j)).Mem n

theorem inKid_disj {A B : Box} (h : A.Disj B) {k : ℕ} {j j' : Fin k} (hjj : j ≠ j') {n : ℤ}
    (hj : InKid A B k j n) : ¬ InKid A B k j' n := by
  rintro (ha' | hb') <;> rcases hj with ha | hb
  · exact disj_place (child_disj k hjj) n ha ha'
  · exact disj_place_of h.symm n hb ha'
  · exact disj_place_of h n ha hb'
  · exact disj_place (child_disj k hjj) n hb hb'

/-- The swap of the `j`-th pair of `k`-children. -/
noncomputable def kidSwap {A B : Box} (h : A.Disj B) (k : ℕ) (j : Fin k) : Perm ℤ :=
  swap (place A (child k j)) (place B (child k j)) (disj_place_of h)

theorem prod_kidSwap_fix {A B : Box} (h : A.Disj B) (k : ℕ) (n : ℤ) :
    ∀ l : List (Fin k), (∀ j ∈ l, ¬ InKid A B k j n) → (l.map (kidSwap h k)).prod n = n
  | [], _ => by rw [List.map_nil, List.prod_nil, Perm.one_apply]
  | j :: l, hl => by
    rw [List.map_cons, List.prod_cons, Perm.mul_apply,
      prod_kidSwap_fix h k n l fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')]
    have hj := hl j List.mem_cons_self
    exact swap_fix _ (fun ha => hj (Or.inl ha)) (fun hb => hj (Or.inr hb))

theorem kidSwap_inKid {A B : Box} (h : A.Disj B) {k : ℕ} {j : Fin k} {n : ℤ}
    (hn : InKid A B k j n) : InKid A B k j (kidSwap h k j n) := by
  rcases hn with ha | hb
  · exact Or.inr ((swap_canon (disj_place_of h)).mem ha)
  · exact Or.inl ((swap_canon' (disj_place_of h)).mem hb)

theorem prod_kidSwap_apply {A B : Box} (h : A.Disj B) (k : ℕ) (j₀ : Fin k) (n : ℤ)
    (hn : InKid A B k j₀ n) :
    ∀ l : List (Fin k), l.Nodup → j₀ ∈ l → (l.map (kidSwap h k)).prod n = kidSwap h k j₀ n
  | [], _, hm => absurd hm List.not_mem_nil
  | j :: l, hnd, hm => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.prod_cons, Perm.mul_apply]
    by_cases hj : j = j₀
    · subst hj
      rw [prod_kidSwap_fix h k n l fun j' hj' =>
        inKid_disj h (fun e => hnd.1 (by rw [e]; exact hj')) hn]
    · have hm' : j₀ ∈ l := (List.mem_cons.1 hm).resolve_left (Ne.symm hj)
      rw [prod_kidSwap_apply h k j₀ n hn l hnd.2 hm']
      have hk := inKid_disj h (Ne.symm hj) (kidSwap_inKid h hn)
      exact swap_fix _ (fun ha => hk (Or.inl ha)) (fun hb => hk (Or.inr hb))

/-- The splitting relation: a swap is the product of the swaps of its `k`-children. -/
theorem swap_split {A B : Box} (h : A.Disj B) (k : ℕ) (hk : 0 < k) :
    ((List.finRange k).map (kidSwap h k)).prod = swap A B h := by
  refine Equiv.ext fun n => ?_
  by_cases hn : ∃ j, InKid A B k j n
  · obtain ⟨j₀, hj₀⟩ := hn
    rw [prod_kidSwap_apply h k j₀ n hj₀ _ (List.nodup_finRange k) (List.mem_finRange j₀)]
    rcases hj₀ with ha | hb
    · exact (swap_canon (disj_place_of h)).agree ((swap_canon h).place _) ha
    · exact (swap_canon' (disj_place_of h)).agree ((swap_canon' h).place _) hb
  · have hn' : ∀ j, ¬ InKid A B k j n := fun j hj => hn ⟨j, hj⟩
    rw [prod_kidSwap_fix h k n _ fun j _ => hn' j]
    have ha : ¬ A.Mem n := fun ha =>
      hn' (classOf k hk (n / A.m)) (Or.inl (mem_place.2 ⟨ha, mem_classOf k hk _⟩))
    have hb : ¬ B.Mem n := fun hb =>
      hn' (classOf k hk (n / B.m)) (Or.inr (mem_place.2 ⟨hb, mem_classOf k hk _⟩))
    exact (swap_fix h ha hb).symm

end GroupApproximation.ClassTransposition.Presentation
