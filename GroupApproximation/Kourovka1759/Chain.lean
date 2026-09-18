import GroupApproximation.Kourovka1759.Meq

/-!
# Chains and types

The chain `tail (k :: l)` splits `ℤ` into `k` classes, splits class `0` by the head of `l`, and so
on down. Splitting any leaf of a chain by `a` gives a partition equivalent to the chain with `a`
inserted below the root (`cl`), by at most three exchanges. Hence chains whose lists are
permutations of each other are equivalent (`chain_perm`), and `Ty P k M` (the multiset `P` is
equivalent to the chain with root `k` and lower arities `M`) depends only on the multiset `M`.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

namespace STree

/-- `tail (a :: l)` splits into `a` classes and continues with `tail l` in class `0`. -/
def tail : List ℕ → STree
  | [] => leaf
  | a :: l => node a fun j => if (j : ℕ) = 0 then tail l else leaf

@[simp] theorem tail_nil : tail [] = leaf := rfl

theorem tail_cons (a : ℕ) (l : List ℕ) :
    tail (a :: l) = node a fun j => if (j : ℕ) = 0 then tail l else leaf := rfl

/-- The children of an `a`-split other than child `0`. -/
def rest (a : ℕ) (ha : 0 < a) : Multiset Box :=
  ∑ j ∈ (Finset.univ : Finset (Fin a)).erase ⟨0, ha⟩, {child a j}

theorem mem_rest {a : ℕ} {ha : 0 < a} {E : Box} :
    E ∈ rest a ha ↔ ∃ j : Fin a, j ≠ ⟨0, ha⟩ ∧ E = child a j := by
  unfold rest
  rw [Multiset.mem_sum]
  constructor
  · rintro ⟨j, hj, hE⟩
    exact ⟨j, (Finset.mem_erase.1 hj).1, Multiset.mem_singleton.1 hE⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩, Multiset.mem_singleton_self _⟩

theorem card_rest (a : ℕ) (ha : 0 < a) : Multiset.card (rest a ha) = a - 1 := by
  rw [rest, Multiset.card_sum]
  simp [Finset.card_erase_of_mem]

theorem ml_tail_cons {a : ℕ} (ha : 0 < a) (l : List ℕ) :
    ml (tail (a :: l)) = (ml (tail l)).map (place (child a ⟨0, ha⟩)) + rest a ha := by
  rw [tail_cons, ml_node, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, ha⟩ : Fin a)), rest]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : (j : ℕ) ≠ 0 := fun h => (Finset.mem_erase.1 hj).1 (Fin.ext h)
  rw [if_neg hj0, ml_leaf, Multiset.map_singleton, place_univ]

theorem ml_tail_single {a : ℕ} (ha : 0 < a) :
    ml (tail [a]) = {child a ⟨0, ha⟩} + rest a ha := by
  rw [ml_tail_cons ha, tail_nil, ml_leaf, Multiset.map_singleton, place_univ]

theorem ml_tail_single_sum (a : ℕ) : ml (tail [a]) = ∑ j : Fin a, {child a j} := by
  rw [tail_cons, ml_node]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tail_nil, ite_self, ml_leaf, Multiset.map_singleton, place_univ]

/-- The one-level split of the box `E` into `a` classes. -/
def spl (a : ℕ) (E : Box) : Multiset Box := (ml (tail [a])).map (place E)

theorem spl_eq {a : ℕ} (ha : 0 < a) (E : Box) :
    spl a E = {place E (child a ⟨0, ha⟩)} + (rest a ha).map (place E) := by
  rw [spl, ml_tail_single ha, Multiset.map_add, Multiset.map_singleton]

theorem card_ml_tail_cons {a : ℕ} (ha : 0 < a) (l : List ℕ) :
    Multiset.card (ml (tail (a :: l))) = Multiset.card (ml (tail l)) + (a - 1) := by
  rw [ml_tail_cons ha, Multiset.card_add, Multiset.card_map, card_rest]

theorem card_ml_tail_replicate (m : ℕ) :
    Multiset.card (ml (tail (List.replicate m 2))) = m + 1 := by
  induction m with
  | zero => simp [ml_leaf]
  | succ m ih => rw [List.replicate_succ, card_ml_tail_cons (by norm_num), ih]

/-- Two exchanges move the contents `T` of `A` under the new split of `E`. -/
theorem two_exchanges {A E X₀ : Box} {R₁ S T : Multiset Box} (hEA : E.Disj A)
    (hS : ∀ x ∈ S, x.Disj X₀) (hR : ∀ x ∈ R₁, x.Disj A ∧ x.Disj E) :
    MEq (T.map (place A) + R₁ + ({place E X₀} + S.map (place E)))
      ((T.map (place X₀) + S).map (place A) + ({E} + R₁)) := by
  have hAB : A.Disj (place E X₀) := disj_place_right hEA.symm X₀
  have hC1 : ∀ x ∈ R₁ + S.map (place E), x.Disj A ∧ x.Disj (place E X₀) := by
    intro x hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact ⟨(hR x hx).1, disj_place_right (hR x hx).2 X₀⟩
    · obtain ⟨Y, hY, rfl⟩ := Multiset.mem_map.1 hx
      exact ⟨disj_place_left hEA Y, disj_place (hS Y hY)⟩
  have h1 := MEq.exchange hAB (R₁ + S.map (place E)) T {univ} hC1
  have h2 := MEq.exchange hEA.symm R₁ {univ} (T.map (place X₀) + S) hR
  refine (MEq.of_eq ?_).trans (h1.trans ((MEq.of_eq ?_).trans (h2.trans (MEq.of_eq ?_))))
  · rw [Multiset.map_singleton, place_univ]
    abel
  · rw [Multiset.map_add (place E), map_place_place]
    abel
  · rw [Multiset.map_singleton, place_univ]
    abel

theorem erase_single_add (E : Box) (R : Multiset Box) : ({E} + R).erase E = R := by
  rw [Multiset.singleton_add, Multiset.erase_cons_head]

theorem mem_single_add (E : Box) (R : Multiset Box) : E ∈ ({E} + R) :=
  Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self E))

/-- Splitting a root leaf `j ≠ 0` of a chain by `a` gives the chain with `a` below the root. -/
theorem cl_root {k : ℕ} (hk0 : 0 < k) (l : List ℕ) {a : ℕ} (ha : 0 < a) {j : Fin k}
    (hj : j ≠ ⟨0, hk0⟩) :
    MEq ((ml (tail (k :: l))).erase (child k j) + spl a (child k j))
      (ml (tail (k :: a :: l))) := by
  have hjm : j ∈ (Finset.univ : Finset (Fin k)).erase ⟨0, hk0⟩ :=
    Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩
  have hR : rest k hk0 = {child k j} +
      ∑ i ∈ ((Finset.univ : Finset (Fin k)).erase ⟨0, hk0⟩).erase j, {child k i} :=
    (Finset.add_sum_erase _ _ hjm).symm
  rw [ml_tail_cons hk0 (a :: l), ml_tail_cons ha l, ml_tail_cons hk0 l, hR, spl_eq ha,
    Multiset.erase_add_right_pos _ (mem_single_add _ _), erase_single_add]
  refine two_exchanges (child_disj k hj) ?_ ?_
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_rest.1 hx
    exact child_disj a hi
  · intro x hx
    rw [Multiset.mem_sum] at hx
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨hij, hi⟩ := Finset.mem_erase.1 hi
    rw [Multiset.mem_singleton.1 hx]
    exact ⟨child_disj k (Finset.mem_erase.1 hi).1, child_disj k hij⟩

/-- **Chain lemma.** Splitting any leaf of a chain by `a` gives a partition equivalent to the
chain with `a` inserted below the root. -/
theorem cl {k : ℕ} (hk : 2 ≤ k) (l : List ℕ) {a : ℕ} (ha : 0 < a) {E : Box}
    (hE : E ∈ ml (tail (k :: l))) :
    MEq ((ml (tail (k :: l))).erase E + spl a E) (ml (tail (k :: a :: l))) := by
  have hk0 : 0 < k := by omega
  have hml := ml_tail_cons hk0 l
  have hE2 := hE
  rw [hml] at hE2
  rcases Multiset.mem_add.1 hE2 with hT | hE'
  · obtain ⟨E₀, -, rfl⟩ := Multiset.mem_map.1 hT
    have hj1 : (⟨1, hk⟩ : Fin k) ≠ ⟨0, hk0⟩ := by
      intro h; simp [Fin.ext_iff] at h
    refine MEq.trans ?_ (cl_root hk0 l ha hj1)
    have hj1m : (⟨1, hk⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)).erase ⟨0, hk0⟩ :=
      Finset.mem_erase.2 ⟨hj1, Finset.mem_univ _⟩
    have hR : rest k hk0 = {child k ⟨1, hk⟩} +
        ∑ i ∈ ((Finset.univ : Finset (Fin k)).erase ⟨0, hk0⟩).erase ⟨1, hk⟩, {child k i} :=
      (Finset.add_sum_erase _ _ hj1m).symm
    have hpd := pd_ml (tail (k :: l))
    have hEF : (place (child k ⟨0, hk0⟩) E₀).Disj (child k ⟨1, hk⟩) :=
      disj_place_left (child_disj k hj1.symm) E₀
    have hC : ∀ x ∈ ((ml (tail l)).map (place (child k ⟨0, hk0⟩))).erase
          (place (child k ⟨0, hk0⟩) E₀) +
        ∑ i ∈ ((Finset.univ : Finset (Fin k)).erase ⟨0, hk0⟩).erase ⟨1, hk⟩, {child k i},
        x.Disj (place (child k ⟨0, hk0⟩) E₀) ∧ x.Disj (child k ⟨1, hk⟩) := by
      intro x hx
      rcases Multiset.mem_add.1 hx with hx | hx
      · have hx' : x ∈ (ml (tail (k :: l))).erase (place (child k ⟨0, hk0⟩) E₀) := by
          rw [hml, Multiset.erase_add_left_pos _ hT]
          exact Multiset.mem_add.2 (Or.inl hx)
        refine ⟨(hpd _ hE x hx').symm, ?_⟩
        obtain ⟨X, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_mem_erase hx)
        exact disj_place_left (child_disj k hj1.symm) X
      · rw [Multiset.mem_sum] at hx
        obtain ⟨i, hi, hx⟩ := hx
        obtain ⟨hi1, hi⟩ := Finset.mem_erase.1 hi
        rw [Multiset.mem_singleton.1 hx]
        exact ⟨disj_place_right (child_disj k (Finset.mem_erase.1 hi).1) E₀, child_disj k hi1⟩
    have hx := MEq.exchange hEF _ (ml (tail [a])) {univ} hC
    have key : ((ml (tail l)).map (place (child k ⟨0, hk0⟩))).erase
        (place (child k ⟨0, hk0⟩) E₀) + {place (child k ⟨0, hk0⟩) E₀} =
        (ml (tail l)).map (place (child k ⟨0, hk0⟩)) := by
      rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hT]
    rw [hml, hR, Multiset.erase_add_left_pos _ hT,
      Multiset.erase_add_right_pos _ (mem_single_add _ _), erase_single_add, spl, spl]
    refine (MEq.of_eq ?_).trans (hx.trans (MEq.of_eq ?_))
    · rw [Multiset.map_singleton, place_univ]
      abel
    · rw [Multiset.map_singleton, place_univ]
      conv_rhs => rw [← key]
      abel
  · obtain ⟨j, hj, rfl⟩ := mem_rest.1 hE'
    exact cl_root hk0 l ha hj

theorem mem_tail_one {k : ℕ} (hk : 2 ≤ k) (l : List ℕ) :
    child k ⟨1, hk⟩ ∈ ml (tail (k :: l)) := by
  rw [ml_tail_cons (by omega : 0 < k)]
  refine Multiset.mem_add.2 (Or.inr (mem_rest.2 ⟨_, ?_, rfl⟩))
  intro h; simp [Fin.ext_iff] at h

theorem exists_mem_tail : ∀ {l : List ℕ}, (∀ a ∈ l, 0 < a) → ∃ X, X ∈ ml (tail l)
  | [], _ => ⟨univ, by simp [ml_leaf]⟩
  | a :: l, h => by
    obtain ⟨X, hX⟩ := exists_mem_tail (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨place (child a ⟨0, h a List.mem_cons_self⟩) X, ?_⟩
    rw [ml_tail_cons (h a List.mem_cons_self)]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ hX))

/-- Chains whose lists are permutations of each other are equivalent. -/
theorem chain_perm {k : ℕ} (hk : 2 ≤ k) {l₁ l₂ : List ℕ} (hp : l₁.Perm l₂) :
    (∀ a ∈ l₁, 0 < a) → MEq (ml (tail (k :: l₁))) (ml (tail (k :: l₂))) := by
  induction hp with
  | nil => intro _; exact MEq.refl _
  | cons x _ ih =>
    intro hl
    have hx := hl x List.mem_cons_self
    obtain ⟨E', hE', hg⟩ :=
      (ih fun a ha => hl a (List.mem_cons_of_mem _ ha)).graft (mem_tail_one hk _)
    exact (cl hk _ hx (mem_tail_one hk _)).symm.trans
      ((hg (ml (tail [x]))).trans (cl hk _ hx hE'))
  | swap x y l =>
    intro hl
    have hy := hl y List.mem_cons_self
    have hx := hl x (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨X, hX⟩ := exists_mem_tail fun a ha =>
      hl a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
    have hk0 : 0 < k := by omega
    have hF := mem_tail_one hk l
    have hG : place (child k ⟨0, hk0⟩) X ∈ ml (tail (k :: l)) := by
      rw [ml_tail_cons hk0]
      exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ hX))
    have hFG : child k ⟨1, hk⟩ ≠ place (child k ⟨0, hk0⟩) X := by
      refine ne_of_disj (disj_place_right (child_disj k ?_) X)
      intro h; simp [Fin.ext_iff] at h
    have hG1 : place (child k ⟨0, hk0⟩) X ∈
        (ml (tail (k :: l))).erase (child k ⟨1, hk⟩) + spl x (child k ⟨1, hk⟩) :=
      Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hFG.symm).2 hG))
    obtain ⟨G', hG', hg1⟩ := (cl hk l hx hF).graft hG1
    have h2 := (hg1 (ml (tail [y]))).trans (cl hk (x :: l) hy hG')
    have hF1 : child k ⟨1, hk⟩ ∈
        (ml (tail (k :: l))).erase (place (child k ⟨0, hk0⟩) X) +
          spl y (place (child k ⟨0, hk0⟩) X) :=
      Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hFG).2 hF))
    obtain ⟨F', hF', hg3⟩ := (cl hk l hy hG).graft hF1
    have h4 := (hg3 (ml (tail [x]))).trans (cl hk (y :: l) hx hF')
    refine h2.symm.trans ((MEq.of_eq ?_).trans h4)
    rw [Multiset.erase_add_left_pos _ ((Multiset.mem_erase_of_ne hFG.symm).2 hG),
      Multiset.erase_add_left_pos _ ((Multiset.mem_erase_of_ne hFG).2 hF),
      Multiset.erase_comm]
    unfold spl
    abel
  | trans p₁ _ ih₁ ih₂ =>
    intro hl
    exact (ih₁ hl).trans (ih₂ fun a ha => hl a (p₁.mem_iff.2 ha))

/-- `P` has type `(k, M)`: it is equivalent to the chain with root arity `k` and lower
arities `M`, and every arity is at least `2`. -/
def Ty (P : Multiset Box) (k : ℕ) (M : Multiset ℕ) : Prop :=
  2 ≤ k ∧ (∀ a ∈ M, 2 ≤ a) ∧ ∃ l : List ℕ, (l : Multiset ℕ) = M ∧ MEq P (ml (tail (k :: l)))

theorem Ty.chain {k : ℕ} (hk : 2 ≤ k) {l : List ℕ} (hl : ∀ a ∈ l, 2 ≤ a) :
    Ty (ml (tail (k :: l))) k l :=
  ⟨hk, fun a ha => hl a (Multiset.mem_coe.1 ha), l, rfl, MEq.refl _⟩

theorem Ty.of_meq {P Q : Multiset Box} {k : ℕ} {M : Multiset ℕ} (h : MEq P Q) (hQ : Ty Q k M) :
    Ty P k M := by
  obtain ⟨hk, hM, l, hl, hm⟩ := hQ
  exact ⟨hk, hM, l, hl, h.trans hm⟩

theorem Ty.congr2 {P P' : Multiset Box} {k : ℕ} {M M' : Multiset ℕ} (h : Ty P k M)
    (hP : P = P') (hM : M = M') : Ty P' k M' := by
  subst hP hM
  exact h

theorem Ty.equi {P Q : Multiset Box} {k : ℕ} {M : Multiset ℕ} (hP : Ty P k M) (hQ : Ty Q k M) :
    MEq P Q := by
  obtain ⟨hk, hM, l₁, rfl, h₁⟩ := hP
  obtain ⟨-, -, l₂, hl, h₂⟩ := hQ
  refine h₁.trans ((chain_perm hk (Multiset.coe_eq_coe.1 hl.symm) fun a ha => ?_).trans h₂.symm)
  have := hM a (Multiset.mem_coe.2 ha)
  omega

theorem Ty.transfer {Z P : Multiset Box} {k k' : ℕ} {M M' : Multiset ℕ} (h₁ : Ty Z k M)
    (h₂ : Ty Z k' M') (hP : Ty P k M) : Ty P k' M' :=
  h₂.of_meq (hP.equi h₁)

theorem Ty.split {P : Multiset Box} {k : ℕ} {M : Multiset ℕ} (h : Ty P k M)
    {E : Box} (hE : E ∈ P) {a : ℕ} (ha : 2 ≤ a) : Ty (P.erase E + spl a E) k (a ::ₘ M) := by
  obtain ⟨hk, hM, l, rfl, hm⟩ := h
  obtain ⟨E', hE', hg⟩ := hm.graft hE
  refine ⟨hk, fun b hb => ?_, a :: l, rfl, (hg (ml (tail [a]))).trans (cl hk l (by omega) hE')⟩
  rcases Multiset.mem_cons.1 hb with rfl | hb
  exacts [ha, hM b hb]

theorem Ty.nonempty {P : Multiset Box} {k : ℕ} {M : Multiset ℕ} (h : Ty P k M) :
    ∃ E, E ∈ P := by
  obtain ⟨hk, -, l, -, hm⟩ := h
  apply Multiset.card_pos_iff_exists_mem.1
  rw [hm.card_eq]
  exact Multiset.card_pos_iff_exists_mem.2 ⟨_, mem_tail_one hk l⟩

end STree

end GroupApproximation.Kourovka1759
