import GroupApproximation.ClassTransposition.Presentation.Moves

/-!
# The comb bases

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

`ell k = (2^k − 1)(2^k)` is the *tail* at depth `k` and `cc k = (2^k − 1)(2^{k+1})`; they are the
two children of `ell k`. The comb with `n + 1` boxes is `[cc 0, …, cc (n-1), ell n]`. Splitting
its tail by 2 gives the next comb (`splitAt_comb_tail`), and the canonical map onto `ell 1`
shifts the comb by one box (`comb_succ_succ`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- The tail box at depth `k`. -/
def ell : ℕ → Box
  | 0 => univ
  | k + 1 => place (ell k) (child 2 1)

/-- The `k`-th tooth of the comb: the first child of `ell k`. -/
def cc (k : ℕ) : Box := place (ell k) (child 2 0)

/-- The comb with `n` boxes. -/
def comb : ℕ → List Box
  | 0 => []
  | n + 1 => (List.range n).map cc ++ [ell n]

theorem comb_succ (n : ℕ) : comb (n + 1) = (List.range n).map cc ++ [ell n] := rfl

@[simp] theorem length_comb (n : ℕ) : (comb n).length = n := by
  cases n <;> simp [comb]

theorem kids_two (E : Box) : kids E 2 = [place E (child 2 0), place E (child 2 1)] := rfl

theorem kids_ell (n : ℕ) : kids (ell n) 2 = [cc n, ell (n + 1)] := rfl

theorem splitAt_append_right (l : List Box) : ∀ (l' : List Box) (i p : ℕ),
    splitAt (l ++ l') (l.length + i) p = l ++ splitAt l' i p := by
  induction l with
  | nil => intro l' i p; simp
  | cons E l ih =>
    intro l' i p
    rw [List.cons_append, List.length_cons, show l.length + 1 + i = (l.length + i) + 1 by omega]
    exact congrArg (E :: ·) (ih l' i p)

/-- Splitting the tail of a comb by 2 gives the next comb. -/
theorem splitAt_comb_tail (n : ℕ) : splitAt (comb (n + 1)) n 2 = comb (n + 2) := by
  have h := splitAt_append_right ((List.range n).map cc) [ell n] 0 2
  simp only [List.length_map, List.length_range, add_zero] at h
  rw [comb_succ, h, comb_succ, List.range_succ, List.map_append, List.append_assoc]
  rfl

theorem isPart_univ : IsPart [univ] :=
  ⟨List.pairwise_singleton _ _, fun n => ⟨univ, List.mem_singleton_self _, univ_mem n⟩⟩

theorem isPart_comb : ∀ n, 0 < n → IsPart (comb n)
  | 0, h => absurd h (lt_irrefl 0)
  | 1, _ => isPart_univ
  | n + 2, _ => by
    rw [← splitAt_comb_tail]
    exact isPart_splitAt (isPart_comb (n + 1) (Nat.succ_pos n)) n (by norm_num)

/-! ### The shift -/

theorem place_ell_one_ell : ∀ k, place (ell 1) (ell k) = ell (k + 1)
  | 0 => place_univ _
  | k + 1 => by
    show place (ell 1) (place (ell k) (child 2 1)) = place (ell (k + 1)) (child 2 1)
    rw [place_assoc, place_ell_one_ell k]

theorem place_ell_one_cc (k : ℕ) : place (ell 1) (cc k) = cc (k + 1) := by
  show place (ell 1) (place (ell k) (child 2 0)) = place (ell (k + 1)) (child 2 0)
  rw [place_assoc, place_ell_one_ell k]

theorem cc_zero : cc 0 = child 2 0 := univ_place _

/-- The comb with `n + 2` boxes is `cc 0` followed by the comb with `n + 1` boxes, moved into
`ell 1`. -/
theorem comb_succ_succ (n : ℕ) : comb (n + 2) = cc 0 :: (comb (n + 1)).map (place (ell 1)) := by
  rw [comb_succ, comb_succ, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons_append,
    List.map_append, List.map_map, List.map_singleton, place_ell_one_ell]
  congr 2
  exact List.map_congr_left fun k _ => (place_ell_one_cc k).symm

end GroupApproximation.ClassTransposition.Presentation
