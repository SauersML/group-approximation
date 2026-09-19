import GroupApproximation.ClassTransposition.Presentation.WinAux

/-!
# Window relations in `H P` at every position and level

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §3).

The window families (a) squares and braids, (d) for a swap and a split of a swapped box, and the
colour exchange (c) hold in `H P` at every position and level. The proof is by induction on the
level:
* at levels `≤ 8` the instance is a relator;
* when the lowest box is `≥ 2`, the instance is the shift of the one a box to the left
  (`eq_up`);
* otherwise the instance stays away from the tail and lives one level down (`eq_stable`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem params_le {x : Inst} (h : ∀ c ∈ x.params, c ≤ 8 ∨ c ∈ P' P) (hB : BddAbove (P' P)) :
    ∀ c ∈ x.params, c ≤ sSup (P' P) + 8 := by
  intro c hc
  rcases h c hc with h | h
  · omega
  · exact le_sSup_P' hB h

theorem params_num {x : Inst} (h : ∀ c ∈ x.params, c ≤ 8) : ∀ c ∈ x.params, c ≤ sSup (P' P) + 8 :=
  fun c hc => (h c hc).trans (Nat.le_add_left _ _)

theorem pos_nil : ∀ m ∈ ([] : List Move), m.Pos := fun _ h => absurd h List.not_mem_nil

/-- Squares of swaps. -/
theorem sq_all :
    ∀ n k, k + 2 ≤ n → toH P n [.swap k, .swap k] = toH P n [] := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hv
    by_cases hn : n ≤ 8
    · exact inst_small (x := .sq n k) (by simp only [Inst.Valid]; omega)
        (params_num (by
          intro c hc
          simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega))
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hk : 2 ≤ k
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact eq_up (u := [.swap k, .swap k]) (v := [])
        (pos_cons (m := .swap k) (show 1 ≤ k by omega)
          (pos_cons (m := .swap k) (show 1 ≤ k by omega) pos_nil))
        pos_nil (ih n (by omega) k (by omega))
    · exact eq_stable (u := [.swap k, .swap k]) (v := [])
        ⟨show k + 2 < n by omega, show k + 2 < n by omega, trivial⟩ trivial
        (ih n (by omega) k (by omega))

/-- Braid relations of swaps. -/
theorem br_all : ∀ n k, k + 3 ≤ n →
    toH P n [.swap k, .swap (k + 1), .swap k] = toH P n [.swap (k + 1), .swap k, .swap (k + 1)] := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hv
    by_cases hn : n ≤ 8
    · exact inst_small (x := .br n k) (by simp only [Inst.Valid]; omega)
        (params_num (by
          intro c hc
          simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl <;> omega))
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hk : 2 ≤ k
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact eq_up (u := [.swap k, .swap (k + 1), .swap k])
        (v := [.swap (k + 1), .swap k, .swap (k + 1)])
        (pos_cons (m := .swap k) (show 1 ≤ k by omega) (pos_cons (m := .swap (k + 1))
          (show 1 ≤ k + 1 by omega) (pos_cons (m := .swap k) (show 1 ≤ k by omega) pos_nil)))
        (pos_cons (m := .swap (k + 1)) (show 1 ≤ k + 1 by omega) (pos_cons (m := .swap k)
          (show 1 ≤ k by omega) (pos_cons (m := .swap (k + 1)) (show 1 ≤ k + 1 by omega) pos_nil)))
        (ih n (by omega) k (by omega))
    · exact eq_stable (u := [.swap k, .swap (k + 1), .swap k])
        (v := [.swap (k + 1), .swap k, .swap (k + 1)])
        ⟨show k + 2 < n by omega, show k + 1 + 2 < n by omega, show k + 2 < n by omega, trivial⟩
        ⟨show k + 1 + 2 < n by omega, show k + 2 < n by omega, show k + 1 + 2 < n by omega,
          trivial⟩
        (ih n (by omega) k (by omega))

/-- (d): a swap followed by a split of the first swapped box. -/
theorem dk_all (hB : BddAbove (P' P)) {p : ℕ} (hp : p ∈ P' P) :
    ∀ n k, k + 2 ≤ n →
      toH P n [.swap k, .split k p] = toH P n (.split (k + 1) p :: swaps k (List.range p)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hv
    by_cases hn : n ≤ 8
    · exact inst_small (x := .dk n k p) (by simp only [Inst.Valid]; exact ⟨hv, hp⟩)
        (params_le (by
          intro c hc
          simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl <;>
            first | exact Or.inl (by omega) | exact Or.inr ‹_›) hB)
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hk : 2 ≤ k
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have h := eq_up (u := [.swap k, .split k p]) (v := .split (k + 1) p :: swaps k (List.range p))
        (pos_cons (m := .swap k) (show 1 ≤ k by omega)
          (pos_cons (m := .split k p) (show 1 ≤ k by omega) pos_nil))
        (pos_cons (m := .split (k + 1) p) (show 1 ≤ k + 1 by omega) (pos_swaps (by omega) _))
        (ih n (by omega) k (by omega))
      simpa only [List.map_cons, List.map_nil, map_up_swaps, Move.up] using h
    · refine eq_stable (u := [.swap k, .split k p]) (v := .split (k + 1) p :: swaps k (List.range p))
        ⟨show k + 2 < n by omega, show k + 1 < n by omega, trivial⟩
        ⟨show k + 1 + 1 < n by omega, ?_⟩ (ih n (by omega) k (by omega))
      rw [lev_split p (by omega)]
      exact frontW_swaps k _ _ fun t ht => by rw [List.mem_range] at ht; omega

/-- (d): a swap followed by a split of the second swapped box. -/
theorem dk1_all (hB : BddAbove (P' P)) {p : ℕ} (hp : p ∈ P' P) :
    ∀ n k, k + 2 ≤ n → toH P n [.swap k, .split (k + 1) p] =
      toH P n (.split k p :: swaps k (List.range p).reverse) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hv
    by_cases hn : n ≤ 8
    · exact inst_small (x := .dk1 n k p) (by simp only [Inst.Valid]; exact ⟨hv, hp⟩)
        (params_le (by
          intro c hc
          simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl <;>
            first | exact Or.inl (by omega) | exact Or.inr ‹_›) hB)
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hk : 2 ≤ k
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have h := eq_up (u := [.swap k, .split (k + 1) p])
        (v := .split k p :: swaps k (List.range p).reverse)
        (pos_cons (m := .swap k) (show 1 ≤ k by omega)
          (pos_cons (m := .split (k + 1) p) (show 1 ≤ k + 1 by omega) pos_nil))
        (pos_cons (m := .split k p) (show 1 ≤ k by omega) (pos_swaps (by omega) _))
        (ih n (by omega) k (by omega))
      simpa only [List.map_cons, List.map_nil, map_up_swaps, Move.up] using h
    · refine eq_stable (u := [.swap k, .split (k + 1) p])
        (v := .split k p :: swaps k (List.range p).reverse)
        ⟨show k + 2 < n by omega, show k + 1 + 1 < n by omega, trivial⟩
        ⟨show k + 1 < n by omega, ?_⟩ (ih n (by omega) k (by omega))
      rw [lev_split p (by omega)]
      exact frontW_swaps k _ _ fun t ht => by
        rw [List.mem_reverse, List.mem_range] at ht; omega

theorem mul_pred_add {p q : ℕ} (hp : 1 ≤ p) : q * (p - 1) + q = p * q := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel, add_one_mul, mul_comm]

/-- (c): the colour exchange. -/
theorem cx_all (hB : BddAbove (P' P)) {p q : ℕ} (hp : p ∈ P' P) (hq : q ∈ P' P) (hpq : p ≠ q)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) : ∀ n i, i < n →
      toH P n (.split i p :: layer i p q) =
        toH P n (.split i q :: layer i q p ++ swaps i (crtWord p q)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hv
    by_cases hn : n ≤ 8
    · exact inst_small (x := .cx n i p q) (by simp only [Inst.Valid]; exact ⟨hv, hp, hq, hpq⟩)
        (params_le (by
          intro c hc
          simp only [Inst.params, Inst.code, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl <;>
            first | exact Or.inl (by omega) | exact Or.inr ‹_›) hB)
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hi : 2 ≤ i
    · obtain ⟨i, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have h := eq_up (u := .split i p :: layer i p q)
        (v := .split i q :: layer i q p ++ swaps i (crtWord p q))
        (pos_cons (m := .split i p) (show 1 ≤ i by omega) (pos_layer (by omega) p q))
        (pos_append (pos_cons (m := .split i q) (show 1 ≤ i by omega) (pos_layer (by omega) q p))
          (pos_swaps (by omega) _))
        (ih n (by omega) i (by omega))
      simpa only [List.map_cons, List.map_append, map_up_layer, map_up_swaps, Move.up] using h
    · refine eq_stable (u := .split i p :: layer i p q)
        (v := .split i q :: layer i q p ++ swaps i (crtWord p q)) ⟨show i + 1 < n by omega, ?_⟩
        ((frontW_append n _ _).2 ⟨⟨show i + 1 < n by omega, ?_⟩, ?_⟩)
        (ih n (by omega) i (by omega))
      · rw [lev_split p (by omega)]
        exact frontW_layer hq1 p i _ (by omega)
      · rw [lev_split q (by omega)]
        exact frontW_layer hp1 q i _ (by omega)
      · rw [levW_cons, lev_split q (by omega), levW_layer hp1 q i _ (by omega)]
        refine frontW_swaps i _ _ fun t ht => ?_
        have h1 := crtWord_lt p q t ht
        have h2 := mul_pred_add (q := q) hp1
        generalize p * q = M at h1 h2 ⊢
        generalize q * (p - 1) = R at h1 h2 ⊢
        omega

end GroupApproximation.ClassTransposition.Presentation
