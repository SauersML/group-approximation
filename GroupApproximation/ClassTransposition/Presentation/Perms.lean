import GroupApproximation.ClassTransposition.Presentation.RelAll
import GroupApproximation.ClassTransposition.Presentation.Coxeter

/-!
# Permutations of boxes in `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

At a fixed level `n`, the swaps `hatH P (.swap k) n` satisfy the Coxeter relations (`isCox_swH`).
So two swap words with the same permutation are equal in `H P` (`toH_swaps_eq_of_perm`), and a
swap word acting on a list of distinct elements determines its permutation
(`perm_eq_of_swapList_eq`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

theorem toH_swaps (n i : ℕ) : ∀ w : List ℕ,
    toH P n (swaps i w) = (w.map fun k => hatH P (.swap (i + k)) n).prod
  | [] => toH_nil n
  | k :: w => by
    show toH P n (.swap (i + k) :: swaps i w) = _
    rw [toH_cons, lev_swap, toH_swaps n i w, List.map_cons, List.prod_cons]

section Cox

variable (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
include hB hP2 hpos

theorem isCox_swH (n : ℕ) : Coxeter.IsCox (fun k => hatH P (.swap k) n) (n - 1) where
  sq k hk := by
    have h := sq_all (P := P) n k (by omega)
    rwa [toH_two, lev_swap, toH_nil] at h
  br k hk := by
    have h := br_all (P := P) n k (by omega)
    simp only [toH_cons, lev_swap, toH_nil, mul_one] at h
    simpa only [mul_assoc] using h
  far k l hkl hl := by
    have h := fsw_all hB hP2 hpos (n := n) hkl (by omega)
    rwa [toH_two, toH_two, lev_swap, lev_swap] at h

/-- Two swap words with the same permutation of `ℕ` are equal in `H P`. -/
theorem toH_swaps_eq_of_perm {n : ℕ} {w w' : List ℕ} (hw : ∀ k ∈ w, k + 1 < n)
    (hw' : ∀ k ∈ w', k + 1 < n)
    (h : (w.map Coxeter.s).prod = (w'.map Coxeter.s).prod) :
    toH P n (swaps 0 w) = toH P n (swaps 0 w') := by
  rw [toH_swaps, toH_swaps]
  simp only [zero_add]
  exact Coxeter.prod_eq_of_perm_eq (isCox_swH hB hP2 hpos n) (fun k hk => by have := hw k hk; omega)
    (fun k hk => by have := hw' k hk; omega) h

end Cox

/-! ### The permutation of a swap word acting on a list -/

/-- Apply a swap word to a list. -/
def swapList {α : Type*} : List α → List ℕ → List α
  | l, [] => l
  | l, k :: w => swapList (swapAt l k) w

theorem getElem?_swapAt {α : Type*} : ∀ (l : List α) (k : ℕ), k + 1 < l.length →
    ∀ x, (swapAt l k)[x]? = l[Coxeter.s k x]?
  | [], _, h, _ => absurd h (by simp)
  | [_], _, h, _ => absurd h (by simp)
  | a :: b :: l, 0, _, x => by
    simp only [swapAt_zero, Coxeter.s, zero_add]
    rcases x with _ | _ | x
    · simp
    · simp
    · rw [swap_apply_of_ne_of_ne (by omega) (by omega)]
      simp
  | a :: l, k + 1, h, x => by
    rw [swapAt_succ]
    rcases x with _ | x
    · simp only [Coxeter.s]
      rw [swap_apply_of_ne_of_ne (by omega) (by omega)]
      simp
    · have hs : Coxeter.s (k + 1) (x + 1) = Coxeter.s k x + 1 := by
        simp only [Coxeter.s, swap_apply_def]
        split_ifs <;> omega
      rw [hs, List.getElem?_cons_succ, List.getElem?_cons_succ,
        getElem?_swapAt l k (by simp at h; omega) x]

theorem length_swapList {α : Type*} : ∀ (l : List α) (w : List ℕ),
    (swapList l w).length = l.length
  | _, [] => rfl
  | l, k :: w => by
    show (swapList (swapAt l k) w).length = l.length
    rw [length_swapList (swapAt l k) w, length_swapAt]

theorem getElem?_swapList {α : Type*} : ∀ (l : List α) (w : List ℕ), (∀ k ∈ w, k + 1 < l.length) →
    ∀ x, (swapList l w)[x]? = l[(w.map Coxeter.s).prod x]?
  | l, [], _, x => rfl
  | l, k :: w, hw, x => by
    show (swapList (swapAt l k) w)[x]? = _
    rw [getElem?_swapList (swapAt l k) w
      (fun k' hk' => by rw [length_swapAt]; exact hw k' (List.mem_cons_of_mem _ hk')),
      getElem?_swapAt l k (hw k List.mem_cons_self), List.map_cons, List.prod_cons,
      Perm.mul_apply]

theorem prod_s_fix {x : ℕ} : ∀ w : List ℕ, (∀ k ∈ w, k + 1 < x) → (w.map Coxeter.s).prod x = x
  | [], _ => rfl
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons, Perm.mul_apply,
      prod_s_fix w fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')]
    have := hw k List.mem_cons_self
    simp only [Coxeter.s]
    exact swap_apply_of_ne_of_ne (by omega) (by omega)

/-- A swap word permuting a list of distinct elements determines its permutation of `ℕ`. -/
theorem perm_eq_of_swapList_eq {α : Type*} {l : List α} (hl : l.Nodup) {w w' : List ℕ}
    (hw : ∀ k ∈ w, k + 1 < l.length) (hw' : ∀ k ∈ w', k + 1 < l.length)
    (h : swapList l w = swapList l w') : (w.map Coxeter.s).prod = (w'.map Coxeter.s).prod := by
  ext x
  rcases Nat.lt_or_ge x l.length with hx | hx
  · have h1 := getElem?_swapList l w hw x
    have h2 := getElem?_swapList l w' hw' x
    rw [h, h2] at h1
    have s1 := Coxeter.supp_prod (N := l.length - 1) w (fun k hk => by have := hw k hk; omega)
    have s2 := Coxeter.supp_prod (N := l.length - 1) w' (fun k hk => by have := hw' k hk; omega)
    have b1 : (w.map Coxeter.s).prod x < l.length := by
      by_contra hc
      have h3 := Coxeter.supp_inv s1 ((w.map Coxeter.s).prod x) (by omega)
      have h4 : ((w.map Coxeter.s).prod)⁻¹ ((w.map Coxeter.s).prod x) = x :=
        ((w.map Coxeter.s).prod).symm_apply_apply x
      rw [h4] at h3
      omega
    have b2 : (w'.map Coxeter.s).prod x < l.length := by
      by_contra hc
      have h3 := Coxeter.supp_inv s2 ((w'.map Coxeter.s).prod x) (by omega)
      have h4 : ((w'.map Coxeter.s).prod)⁻¹ ((w'.map Coxeter.s).prod x) = x :=
        ((w'.map Coxeter.s).prod).symm_apply_apply x
      rw [h4] at h3
      omega
    rw [List.getElem?_eq_getElem b1, List.getElem?_eq_getElem b2, Option.some_inj] at h1
    exact ((List.Nodup.getElem_inj_iff hl).1 h1.symm)
  · rw [prod_s_fix w fun k hk => by have := hw k hk; omega,
      prod_s_fix w' fun k hk => by have := hw' k hk; omega]

end GroupApproximation.ClassTransposition.Presentation
