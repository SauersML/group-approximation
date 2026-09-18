import GroupApproximation.Kourovka1759.Graft

/-!
# The binary normal form

The `k`-split of `ℤ` is equivalent to a binary tree with `k` leaves. Refine both by the tree
`x = b(a, b)` (split in two, then the first half by `k` and the second by `2`); three
commutations make the types agree, and cancellation removes `x`. Replacing every arity by
binary splits then shows that two partitions with types and the same number of pieces are
equivalent.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

namespace STree

theorem wf_node {k : ℕ} {c : Fin k → STree} : WF (node k c) ↔ 2 ≤ k ∧ ∀ j, WF (c j) := Iff.rfl

theorem wf_leaf : WF leaf := True.intro

theorem wf_tail : ∀ {l : List ℕ}, (∀ a ∈ l, 2 ≤ a) → WF (tail l)
  | [], _ => wf_leaf
  | a :: l, h => by
    rw [tail_cons, wf_node]
    refine ⟨h a List.mem_cons_self, fun j => ?_⟩
    split_ifs
    · exact wf_tail fun b hb => h b (List.mem_cons_of_mem _ hb)
    · exact wf_leaf

/-- The tree `b(a, b)`: split into two classes, then the first by `k` and the second by `2`. -/
def xTree (k : ℕ) : STree := node 2 fun j => if (j : ℕ) = 0 then tail [k] else tail [2]

theorem wf_xTree {k : ℕ} (hk : 2 ≤ k) : WF (xTree k) := by
  rw [xTree, wf_node]
  refine ⟨le_refl 2, fun j => ?_⟩
  split_ifs
  · exact wf_tail (by simpa using hk)
  · exact wf_tail (by simp)

theorem ml_xTree (k : ℕ) : ml (xTree k) = spl k (child 2 0) + spl 2 (child 2 1) := by
  rw [xTree, ml_node, Fin.sum_univ_two] <;> rfl

theorem ml_tail_two (k : ℕ) : ml (tail [2, k]) = spl k (child 2 0) + {child 2 1} := by
  rw [tail_cons, ml_node, Fin.sum_univ_two]
  show spl k (child 2 0) + (ml leaf).map (place (child 2 1)) = _
  rw [ml_leaf, Multiset.map_singleton, place_univ]

theorem ty_xTree {k : ℕ} (hk : 2 ≤ k) : Ty (ml (xTree k)) 2 (2 ::ₘ {k}) := by
  have hC := Ty.chain (le_refl 2) (l := [k]) (by simpa using hk)
  have hc1 : child 2 1 ∈ ml (tail [2, k]) := mem_tail_one (le_refl 2) [k]
  refine (hC.split hc1 (le_refl 2)).congr2 ?_ (by rw [Multiset.coe_singleton])
  rw [ml_tail_two, ml_xTree, Multiset.erase_add_right_pos _ (Multiset.mem_singleton_self _),
    Multiset.erase_singleton, add_zero]

theorem ty_subst {s t : STree} {r q : ℕ} {M N : Multiset ℕ} (hs : Ty (ml s) r M)
    (ht : Ty (ml t) q N) :
    Ty (ml (subst s t)) r (Multiset.card (ml s) • (q ::ₘ N) + M) := by
  rw [ml_subst]
  refine (hs.bind (fun _ => ml t) (fun _ => q) (fun _ => N) fun _ _ => ht).congr2 rfl ?_
  rw [bind_const]

/-- **Base.** The `k`-split of `ℤ` has the type of a binary tree with `k` leaves. -/
theorem ty_split_binary {k : ℕ} (hk : 2 ≤ k) :
    Ty (ml (tail [k])) 2 (Multiset.replicate (k - 2) 2) := by
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · obtain rfl : k = 2 := by omega
    exact (Ty.chain (le_refl 2) (l := []) (by simp)).congr2 rfl (by simp)
  have hu : Ty (ml (tail [k])) k 0 :=
    (Ty.chain hk (l := []) (by simp)).congr2 rfl Multiset.coe_nil
  have hv : Ty (ml (tail (2 :: List.replicate (k - 2) 2))) 2 (Multiset.replicate (k - 2) 2) :=
    Ty.chain (le_refl 2) (by simp)
  have hX := ty_xTree hk
  have cu : Multiset.card (ml (tail [k])) = k := card_ml_tail_single (by omega)
  have cv : Multiset.card (ml (tail (2 :: List.replicate (k - 2) 2))) = k := by
    rw [← List.replicate_succ, card_ml_tail_replicate]
    omega
  have hU := ty_subst hu hX
  have hV := ty_subst hv hX
  rw [cu] at hU
  rw [cv] at hV
  have h1 := Ty.comm_root (q := 2) (M := Multiset.replicate k 2 + Multiset.replicate k k)
    (hU.congr2 rfl (by
      ext a
      simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_replicate,
        Multiset.count_nsmul, Multiset.count_singleton, Multiset.count_zero]
      split_ifs <;> omega)) (le_refl 2)
  have h2 := Ty.comm_below (q := 2) (p := k)
    (M := Multiset.replicate (k - 1) 2 + Multiset.replicate k k)
    (h1.congr2 rfl (by
      ext a
      simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_replicate]
      split_ifs <;> omega)) hk
  have h3' := Ty.comm_below (q := 2) (p := k)
    (M := Multiset.replicate (2 * k - 2) 2 + Multiset.replicate (k - 1) k)
    (h2.congr2 rfl (by
      ext a
      simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_replicate]
      split_ifs <;> omega)) hk
  have hmeq := (h3'.congr2 rfl (by
      ext a
      simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_replicate,
        Multiset.count_nsmul, Multiset.count_singleton, Multiset.count_zero]
      split_ifs <;> omega)).equi hV
  exact hv.of_meq (cancel_tree (wf_xTree hk) (cu.trans cv.symm) hmeq)

/-- A lower arity `a` can be replaced by `a - 1` binary splits. -/
theorem Ty.binarize {P : Multiset Box} {r a : ℕ} {M : Multiset ℕ} (h : Ty P r (a ::ₘ M)) :
    Ty P r (Multiset.replicate (a - 1) 2 + M) := by
  have hr := h.1
  have ha : 2 ≤ a := h.2.1 a (Multiset.mem_cons_self _ _)
  have hM : ∀ b ∈ M.toList, 2 ≤ b := fun b hb =>
    h.2.1 b (Multiset.mem_cons_of_mem (Multiset.mem_toList.1 hb))
  have hC := Ty.chain hr hM
  rw [Multiset.coe_toList] at hC
  obtain ⟨E, hE⟩ := hC.nonempty
  have g1 := hC.graft hE ((Ty.chain ha (l := []) (by simp)).congr2 rfl Multiset.coe_nil)
  have g2 := hC.graft hE (ty_split_binary ha)
  refine Ty.transfer (g1.congr2 rfl ?_) (g2.congr2 rfl ?_) h
  · rw [Multiset.cons_add, zero_add]
  · rw [← Multiset.replicate_succ]
    have : a - 2 + 1 = a - 1 := by omega
    rw [this]

/-- The root arity `k` can be replaced by a binary root and `k - 2` binary splits. -/
theorem Ty.binarize_root {P : Multiset Box} {k : ℕ} {M : Multiset ℕ} (h : Ty P k M) :
    Ty P 2 (Multiset.replicate (k - 2) 2 + M) := by
  have hk := h.1
  have hk0 : 0 < k := by omega
  have hM : ∀ b ∈ M.toList, 2 ≤ b := fun b hb => h.2.1 b (Multiset.mem_toList.1 hb)
  have hZ : ml (tail (k :: M.toList)) = (ml (tail [k])).erase (child k ⟨0, hk0⟩) +
      (ml (tail M.toList)).map (place (child k ⟨0, hk0⟩)) := by
    rw [ml_tail_cons hk0 M.toList, ml_tail_single hk0, erase_single_add, add_comm]
  have hc0 : child k ⟨0, hk0⟩ ∈ ml (tail [k]) := by
    rw [ml_tail_single hk0]
    exact mem_single_add _ _
  have g1 := Ty.graft_chain M.toList hM (ty_split_binary hk) hc0
  have hC := Ty.chain hk hM
  rw [Multiset.coe_toList] at g1 hC
  rw [hZ] at hC
  exact Ty.transfer hC (g1.congr2 rfl (add_comm _ _)) h

theorem Ty.binary_aux (M : Multiset ℕ) : ∀ {P : Multiset Box} {m : ℕ},
    Ty P 2 (Multiset.replicate m 2 + M) → ∃ n, Ty P 2 (Multiset.replicate n 2) := by
  induction M using Multiset.induction_on with
  | empty => intro P m h; exact ⟨m, by simpa using h⟩
  | cons a M ih =>
    intro P m h
    have h1 := (h.congr2 rfl (Multiset.add_cons _ _ _)).binarize
    exact ih (m := a - 1 + m) (h1.congr2 rfl (by rw [Multiset.replicate_add, add_assoc]))

/-- Every partition with a type is equivalent to a binary tree. -/
theorem Ty.binary {P : Multiset Box} {k : ℕ} {M : Multiset ℕ} (h : Ty P k M) :
    ∃ n, Ty P 2 (Multiset.replicate n 2) :=
  Ty.binary_aux M h.binarize_root

/-- Two partitions with types and the same number of pieces are equivalent. -/
theorem Ty.meq_of_card {P Q : Multiset Box} {k k' : ℕ} {M M' : Multiset ℕ} (hP : Ty P k M)
    (hQ : Ty Q k' M') (hc : Multiset.card P = Multiset.card Q) : MEq P Q := by
  obtain ⟨m, hm⟩ := hP.binary
  obtain ⟨n, hn⟩ := hQ.binary
  have hb : ∀ j, Ty (ml (tail (2 :: List.replicate j 2))) 2 (Multiset.replicate j 2) :=
    fun j => Ty.chain (le_refl 2) (by simp)
  have cb : ∀ j, Multiset.card (ml (tail (2 :: List.replicate j 2))) = j + 2 := fun j => by
    rw [← List.replicate_succ, card_ml_tail_replicate] <;> omega
  have h1 := (hm.equi (hb m)).card_eq
  have h2 := (hn.equi (hb n)).card_eq
  rw [cb] at h1 h2
  obtain rfl : m = n := by omega
  exact hm.equi hn

end STree

end GroupApproximation.Kourovka1759
