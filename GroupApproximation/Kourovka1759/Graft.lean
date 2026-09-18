import GroupApproximation.Kourovka1759.Chain

/-!
# Grafting, commutation and cancellation

Grafting a partition of type `(q, N)` into a leaf of a partition of type `(k, M)` gives type
`(k, q + N + M)`. The `k`-split with every class split by `q` is the `q`-split with every class
split by `k`, since both are the `kq`-split; this changes the type at the root and below it.
Finally, a common refinement of two trees by the same tree cancels.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

namespace STree

theorem fsum_bind {ι α β : Type*} (s : Finset ι) (f : ι → Multiset α) (G : α → Multiset β) :
    (∑ i ∈ s, f i).bind G = ∑ i ∈ s, (f i).bind G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.add_bind, ih]

theorem bind_const {α β : Type*} (P : Multiset α) (S : Multiset β) :
    (P.bind fun _ => S) = Multiset.card P • S := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
    rw [Multiset.cons_bind, ih, Multiset.card_cons, succ_nsmul]
    abel

theorem card_ml_tail_single {k : ℕ} (hk : 0 < k) : Multiset.card (ml (tail [k])) = k := by
  rw [card_ml_tail_cons hk, tail_nil, ml_leaf, Multiset.card_singleton]
  omega

theorem mem_ml_tail_single {k : ℕ} {x : Box} : x ∈ ml (tail [k]) ↔ x.m = k := by
  rw [ml_tail_single_sum, Multiset.mem_sum]
  constructor
  · rintro ⟨j, -, hx⟩
    exact (congrArg Box.m (Multiset.mem_singleton.1 hx)).trans rfl
  · intro h
    obtain ⟨j, rfl⟩ := eq_child h
    exact ⟨j, Finset.mem_univ _, Multiset.mem_singleton_self _⟩

/-- Grafting a chain into a leaf adds its arities to the type. -/
theorem Ty.graft_chain (l : List ℕ) : ∀ {P : Multiset Box} {k : ℕ} {M : Multiset ℕ} {E : Box},
    (∀ a ∈ l, 2 ≤ a) → Ty P k M → E ∈ P →
    Ty (P.erase E + (ml (tail l)).map (place E)) k (↑l + M) := by
  induction l with
  | nil =>
    intro P k M E _ h hE
    refine h.congr2 ?_ ?_
    · rw [tail_nil, ml_leaf, Multiset.map_singleton, place_univ, add_comm, Multiset.singleton_add,
        Multiset.cons_erase hE]
    · rw [Multiset.coe_nil, zero_add]
  | cons a l ih =>
    intro P k M E hl h hE
    have ha : 2 ≤ a := hl a List.mem_cons_self
    have ha0 : 0 < a := by omega
    have h1 := h.split hE ha
    rw [spl_eq ha0] at h1
    have hE' : place E (child a ⟨0, ha0⟩) ∈
        P.erase E + ({place E (child a ⟨0, ha0⟩)} + (rest a ha0).map (place E)) :=
      Multiset.mem_add.2 (Or.inr (mem_single_add _ _))
    refine (ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)) h1 hE').congr2 ?_ ?_
    · rw [Multiset.erase_add_right_pos _ (mem_single_add _ _), erase_single_add,
        ml_tail_cons ha0 l, Multiset.map_add, map_place_place]
      abel
    · rw [← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]

/-- **Graft.** Grafting a partition of type `(q, N)` into a leaf. -/
theorem Ty.graft {P Q : Multiset Box} {k q : ℕ} {M N : Multiset ℕ} {E : Box}
    (hP : Ty P k M) (hE : E ∈ P) (hQ : Ty Q q N) :
    Ty (P.erase E + Q.map (place E)) k ((q ::ₘ N) + M) := by
  obtain ⟨hk, hM, l, rfl, hPC⟩ := hP
  obtain ⟨hq, hN, n, rfl, hQC⟩ := hQ
  obtain ⟨E', hE', hg⟩ := hPC.graft hE
  have hloc := MEq.local_box (C₀ := (ml (tail (k :: l))).erase E') (N := E')
    (fun x hx => (pd_ml _ E' hE' x hx).symm) hQC
  have hT := Ty.graft_chain (q :: n) (fun a ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hq
      · exact hN a (Multiset.mem_coe.2 ha))
    (Ty.chain hk fun a ha => hM a (Multiset.mem_coe.2 ha)) hE'
  exact Ty.of_meq ((hg Q).trans hloc) (hT.congr2 rfl rfl)

/-- **Graft everywhere.** Grafting a partition of type `(q E, N E)` into every leaf `E`. -/
theorem Ty.bind {P : Multiset Box} {r : ℕ} {M : Multiset ℕ} (hP : Ty P r M)
    (F : Box → Multiset Box) (q : Box → ℕ) (N : Box → Multiset ℕ)
    (hF : ∀ E ∈ P, Ty (F E) (q E) (N E)) :
    Ty (P.bind fun E => (F E).map (place E)) r ((P.bind fun E => q E ::ₘ N E) + M) := by
  have key : ∀ S R : Multiset Box, S + R = P →
      Ty (R + S.bind fun E => (F E).map (place E)) r ((S.bind fun E => q E ::ₘ N E) + M) := by
    intro S
    induction S using Multiset.induction_on with
    | empty =>
      intro R hR
      rw [zero_add] at hR
      subst hR
      simpa only [Multiset.zero_bind, add_zero, zero_add] using hP
    | cons a S ih =>
      intro R hR
      have ha : a ∈ P := by
        rw [← hR]
        exact Multiset.mem_add.2 (Or.inl (Multiset.mem_cons_self a S))
      have h1 := ih (a ::ₘ R) (by rw [← hR, Multiset.add_cons, Multiset.cons_add])
      have h2 := h1.graft (Multiset.mem_add.2 (Or.inl (Multiset.mem_cons_self a R))) (hF a ha)
      refine h2.congr2 ?_ ?_
      · simp only [Multiset.cons_add, Multiset.erase_cons_head, Multiset.cons_bind]
        abel
      · simp only [Multiset.cons_bind]
        abel
  have := key P 0 (add_zero P)
  rwa [zero_add] at this

/-! ### Commutation -/

/-- The `k`-split of `ℤ` with every class split by `q`. -/
def dsplit (k q : ℕ) : Multiset Box := ∑ j : Fin k, (ml (tail [q])).map (place (child k j))

theorem dsplit_eq_ml (k q : ℕ) : dsplit k q = ml (node k fun _ => tail [q]) := by
  rw [ml_node, dsplit]

theorem mem_dsplit {k q : ℕ} (hk : 0 < k) {x : Box} : x ∈ dsplit k q ↔ x.m = (q : ℤ) * k := by
  rw [dsplit, Multiset.mem_sum]
  constructor
  · rintro ⟨j, -, hx⟩
    obtain ⟨Y, hY, rfl⟩ := Multiset.mem_map.1 hx
    rw [mem_ml_tail_single] at hY
    rw [place_m, hY, child_m]
  · intro h
    have hdiv : (child k (classOf k hk x.r)).m ∣ x.m := ⟨q, by rw [h, child_m]; ring⟩
    obtain ⟨Y, hY⟩ := eq_place (mem_classOf k hk x.r) hdiv
    refine ⟨classOf k hk x.r, Finset.mem_univ _, Multiset.mem_map.2 ⟨Y, ?_, hY.symm⟩⟩
    rw [mem_ml_tail_single]
    have h2 : x.m = Y.m * k := (congrArg Box.m hY).trans rfl
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    exact mul_right_cancel₀ hk' (h2.symm.trans h)

theorem nodup_dsplit (k q : ℕ) : (dsplit k q).Nodup := by
  rw [dsplit_eq_ml]
  exact (pd_ml _).nodup

theorem dsplit_comm {k q : ℕ} (hk : 0 < k) (hq : 0 < q) : dsplit k q = dsplit q k := by
  rw [Multiset.Nodup.ext (nodup_dsplit k q) (nodup_dsplit q k)]
  intro x
  rw [mem_dsplit hk, mem_dsplit hq, mul_comm]

theorem ty_dsplit {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q) :
    Ty (dsplit k q) k (Multiset.replicate k q) := by
  have h := (Ty.chain hk (l := []) (by simp)).bind (fun _ => ml (tail [q])) (fun _ => q)
    (fun _ => 0) (fun _ _ => (Ty.chain hq (l := []) (by simp)).congr2 rfl Multiset.coe_nil)
  refine h.congr2 ?_ ?_
  · rw [ml_tail_single_sum k, fsum_bind, dsplit]
    exact Finset.sum_congr rfl fun j _ => Multiset.singleton_bind _ _
  · rw [bind_const, Multiset.coe_nil, add_zero, card_ml_tail_single (k := k) (by omega),
      Multiset.cons_zero, Multiset.nsmul_singleton]

/-- **Root commutation.** -/
theorem Ty.comm_root {P : Multiset Box} {k q : ℕ} {M : Multiset ℕ}
    (h : Ty P k (Multiset.replicate k q + M)) (hq : 2 ≤ q) :
    Ty P q (Multiset.replicate q k + M) := by
  have hk := h.1
  have hM : ∀ a ∈ M.toList, 2 ≤ a := fun a ha =>
    h.2.1 a (Multiset.mem_add.2 (Or.inr (Multiset.mem_toList.1 ha)))
  have h1 := ty_dsplit hk hq
  have h2 : Ty (dsplit k q) q (Multiset.replicate q k) := by
    rw [dsplit_comm (k := k) (q := q) (by omega) (by omega)]
    exact ty_dsplit hq hk
  obtain ⟨E, hE⟩ := h1.nonempty
  have g1 := Ty.graft_chain M.toList hM h1 hE
  have g2 := Ty.graft_chain M.toList hM h2 hE
  rw [Multiset.coe_toList] at g1 g2
  exact Ty.transfer (g1.congr2 rfl (add_comm _ _)) (g2.congr2 rfl (add_comm _ _)) h

/-- **Commutation below the root.** -/
theorem Ty.comm_below {P : Multiset Box} {r q p : ℕ} {M : Multiset ℕ}
    (h : Ty P r (q ::ₘ (Multiset.replicate q p + M))) (hp : 2 ≤ p) :
    Ty P r (p ::ₘ (Multiset.replicate p q + M)) := by
  have hr := h.1
  have hq : 2 ≤ q := h.2.1 q (Multiset.mem_cons_self _ _)
  have hM : ∀ a ∈ M.toList, 2 ≤ a := fun a ha => h.2.1 a (Multiset.mem_cons_of_mem
    (Multiset.mem_add.2 (Or.inr (Multiset.mem_toList.1 ha))))
  have hC := Ty.chain hr hM
  rw [Multiset.coe_toList] at hC
  obtain ⟨E, hE⟩ := hC.nonempty
  have g1 := hC.graft hE (ty_dsplit hq hp)
  have g2 := hC.graft hE (ty_dsplit hp hq)
  rw [dsplit_comm (k := p) (q := q) (by omega) (by omega)] at g2
  refine Ty.transfer (g1.congr2 rfl ?_) (g2.congr2 rfl ?_) h
  · rw [Multiset.cons_add]
  · rw [Multiset.cons_add]

/-! ### Cancellation -/

/-- `subst s t` is the tree `s` with the tree `t` grafted into every leaf. -/
def subst : STree → STree → STree
  | leaf, t => t
  | node k c, t => node k fun j => subst (c j) t

theorem ml_subst (t : STree) : ∀ s : STree,
    ml (subst s t) = (ml s).bind fun V => (ml t).map (place V)
  | leaf => by
    show ml t = _
    have h : (ml t).map (place univ) = ml t := by
      conv_rhs => rw [← Multiset.map_id (ml t)]
      exact Multiset.map_congr rfl fun X _ => univ_place X
    rw [ml_leaf, Multiset.singleton_bind, h]
  | node k c => by
    rw [subst, ml_node, ml_node, fsum_bind]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ml_subst t (c j), Multiset.map_bind, Multiset.bind_map]
    exact Multiset.bind_congr fun V _ => map_place_place _ _ _

/-- **Cancellation.** Two trees whose refinements by the same tree are equivalent, and which
have the same number of leaves, are equivalent. -/
theorem cancel_tree {s₁ s₂ t : STree} (ht : WF t)
    (hlen : Multiset.card (ml s₁) = Multiset.card (ml s₂))
    (h : MEq (ml (subst s₁ t)) (ml (subst s₂ t))) : MEq (ml s₁) (ml s₂) := by
  have hp : ∀ s, (subst s t).leaves.Perm (s.leaves.flatMap fun V => t.leaves.map (place V)) :=
    fun s => Multiset.coe_eq_coe.1 (by rw [← Multiset.coe_bind]; exact ml_subst t s)
  refine MEq.of_equi (Equi.cancel (x := t.leaves) (cover t ht) ?_ ?_ ?_)
  · simpa [ml] using hlen
  · exact ((hp s₂).pairwise_iff (fun h => h.symm)).1 (pairwise (subst s₂ t))
  · exact ((MEq.to_equi h).perm_left (hp s₁)).perm_right (hp s₂)

end STree

end GroupApproximation.Kourovka1759
