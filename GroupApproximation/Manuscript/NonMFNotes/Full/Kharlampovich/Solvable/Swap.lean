import Mathlib.GroupTheory.Subgroup.Centralizer
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.Star
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Solvable.Closure

/-!
# Swapping `a_n` and `ã_n` under an `x`-letter

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex` (Kharlampovich--Myasnikov--
Sapir, arXiv:1204.6506, Sec. 4, proof of Lemma `lT`).

* `swap_a`, `swap_a'`: G6 extends from `x_{q_j}` to `x_{j,S}` for `0, n+1 ∉ S`, i.e.
  `ã_n a_n⁻¹` commutes with `x_{j,S}` (induction on `S` via G5 a) and G2).
* `conj_C`: for `S` without letters `A_{n+1}` and `g` in the (abelian, G1) group `H_s` of small
  letters, `x_{j,S}^g = x_{j,S}^p` with `p ∈ ⟨a_n, a'_n⟩`.
* `conj_F`: for `0 ∉ S` and `g ∈ H_s`, `x_{j,S}^g = x_{j,S}^h` with `h ∈ H_s` commuting with every
  `A_{m+1}`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Sol

open Forward

variable {K N : ℕ} (M : Minsky.Machine K N)

/-- The small letters `a_n, a'_n, ã_n, ã'_n`. -/
def smallSet : Set (KhGroup M) := {g | ∃ s : KhGen K N, s.IsSmall ∧ g = kLet M s}

theorem small_mem {s : KhGen K N} (hs : s.IsSmall) : kLet M s ∈ Subgroup.closure (smallSet M) :=
  Subgroup.subset_closure ⟨s, hs, rfl⟩

theorem smallSet_comm : ∀ x ∈ smallSet M, ∀ y ∈ smallSet M, Commute x y := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  exact commute_small M hs ht

/-- The elements commuting with every `A_{m+1}`. -/
def centA : Subgroup (KhGroup M) :=
  Subgroup.centralizer (Set.range fun m : Fin K => kLet M (.bigA m.succ))

theorem commute_of_mem_centA {h : KhGroup M} (hh : h ∈ centA M) (m : Fin K) :
    Commute (kLet M (.bigA m.succ)) h :=
  Subgroup.mem_centralizer_iff.mp hh (kLet M (.bigA m.succ)) ⟨m, rfl⟩

theorem block0_mem_centA {s : KhGen K N} (hs : s.block = some 0) : kLet M s ∈ centA M := by
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨m, rfl⟩
  exact (commute_block M (s := .bigA m.succ) (t := s) rfl hs (Fin.succ_ne_zero m)).eq

/-- G6 generalized: `u v⁻¹` commutes with `x_{j,S}` for `u` in block `0`, `v` in block `m`. -/
theorem commute_swap_aux (j : Fin (N + 1)) {u v : KhGen K N} {m : Fin (K + 1)}
    (hu : u.block = some 0) (hv : v.block = some m)
    (hbase : (kLet M v)⁻¹ * kLet M (.x j ∅) * kLet M v =
      (kLet M u)⁻¹ * kLet M (.x j ∅) * kLet M u)
    (S : Finset (Fin (K + 1))) :
    0 ∉ S → m ∉ S → Commute (kLet M u * (kLet M v)⁻¹) (kLet M (.x j S)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    show kLet M u * (kLet M v)⁻¹ * kLet M (.x j ∅) =
      kLet M (.x j ∅) * (kLet M u * (kLet M v)⁻¹)
    calc kLet M u * (kLet M v)⁻¹ * kLet M (.x j ∅)
        = kLet M u * ((kLet M v)⁻¹ * kLet M (.x j ∅) * kLet M v) * (kLet M v)⁻¹ := by group
      _ = kLet M u * ((kLet M u)⁻¹ * kLet M (.x j ∅) * kLet M u) * (kLet M v)⁻¹ := by
          rw [hbase]
      _ = kLet M (.x j ∅) * (kLet M u * (kLet M v)⁻¹) := by group
  | insert i S hi ih =>
    intro h0 hm
    have h0' : (0 : Fin (K + 1)) ∉ S := fun h => h0 (Finset.mem_insert_of_mem h)
    have hm' : m ∉ S := fun h => hm (Finset.mem_insert_of_mem h)
    have hi0 : (0 : Fin (K + 1)) ≠ i := by
      rintro rfl
      exact h0 (Finset.mem_insert_self _ S)
    have him : m ≠ i := by
      rintro rfl
      exact hm (Finset.mem_insert_self _ S)
    have hA : Commute (kLet M u * (kLet M v)⁻¹) (kLet M (.bigA i)) :=
      (commute_block M (t := .bigA i) hu rfl hi0).mul_left
        (commute_block M (t := .bigA i) hv rfl him).inv_left
    have hX := ih h0' hm'
    rw [x_insert M j S hi]
    exact ((hX.inv_right.mul_right hA.inv_right).mul_right hX).mul_right hA

theorem swap_a (j : Fin (N + 1)) (n : Fin K) (S : Finset (Fin (K + 1))) (h0 : 0 ∉ S)
    (hn : n.succ ∉ S) : Commute (kLet M (.ta n) * (kLet M (.a n))⁻¹) (kLet M (.x j S)) :=
  commute_swap_aux M j (u := .ta n) (v := .a n) rfl rfl (x_empty_a M j n) S h0 hn

theorem swap_a' (j : Fin (N + 1)) (n : Fin K) (S : Finset (Fin (K + 1))) (h0 : 0 ∉ S)
    (hn : n.succ ∉ S) : Commute (kLet M (.ta' n) * (kLet M (.a' n))⁻¹) (kLet M (.x j S)) :=
  commute_swap_aux M j (u := .ta' n) (v := .a' n) rfl rfl (x_empty_a' M j n) S h0 hn

/-- Splitting of the small letters for `C`: `c` commutes with `x_{j,S}`, `h ∈ ⟨a, a'⟩`. -/
theorem hdecC (j : Fin (N + 1)) {S : Finset (Fin (K + 1))} (hS : ∀ n : Fin K, n.succ ∉ S) :
    ∀ x ∈ smallSet M, ∃ c h : KhGroup M, c ∈ Subgroup.closure (smallSet M) ∧
      h ∈ Subgroup.closure (smallSet M) ∧ Commute c (kLet M (.x j S)) ∧ h ∈ aSub M ∧
      x = c * h := by
  rintro _ ⟨s, hs, rfl⟩
  cases s with
  | x _ _ => exact (hs : False).elim
  | bigA _ => exact (hs : False).elim
  | a n => exact ⟨1, _, one_mem _, small_mem M (s := .a n) trivial, Commute.one_left _,
      a_mem_aSub M n, (one_mul _).symm⟩
  | a' n => exact ⟨1, _, one_mem _, small_mem M (s := .a' n) trivial, Commute.one_left _,
      a'_mem_aSub M n, (one_mul _).symm⟩
  | ta n =>
    by_cases h0 : (0 : Fin (K + 1)) ∈ S
    · exact ⟨_, 1, small_mem M (s := .ta n) trivial, one_mem _,
        (commute_x_block M j (s := .ta n) h0 rfl).symm, one_mem _, (mul_one _).symm⟩
    · exact ⟨kLet M (.ta n) * (kLet M (.a n))⁻¹, kLet M (.a n),
        mul_mem (small_mem M (s := .ta n) trivial) (inv_mem (small_mem M (s := .a n) trivial)),
        small_mem M (s := .a n) trivial, swap_a M j n S h0 (hS n), a_mem_aSub M n,
        (inv_mul_cancel_right _ _).symm⟩
  | ta' n =>
    by_cases h0 : (0 : Fin (K + 1)) ∈ S
    · exact ⟨_, 1, small_mem M (s := .ta' n) trivial, one_mem _,
        (commute_x_block M j (s := .ta' n) h0 rfl).symm, one_mem _, (mul_one _).symm⟩
    · exact ⟨kLet M (.ta' n) * (kLet M (.a' n))⁻¹, kLet M (.a' n),
        mul_mem (small_mem M (s := .ta' n) trivial)
          (inv_mem (small_mem M (s := .a' n) trivial)),
        small_mem M (s := .a' n) trivial, swap_a' M j n S h0 (hS n), a'_mem_aSub M n,
        (inv_mul_cancel_right _ _).symm⟩

/-- Splitting of the small letters for `F`: `c` commutes with `x_{j,S}`, `h` with all
`A_{m+1}`. -/
theorem hdecF (j : Fin (N + 1)) {S : Finset (Fin (K + 1))} (h0 : (0 : Fin (K + 1)) ∉ S) :
    ∀ x ∈ smallSet M, ∃ c h : KhGroup M, c ∈ Subgroup.closure (smallSet M) ∧
      h ∈ Subgroup.closure (smallSet M) ∧ Commute c (kLet M (.x j S)) ∧ h ∈ centA M ∧
      x = c * h := by
  rintro _ ⟨s, hs, rfl⟩
  cases s with
  | x _ _ => exact (hs : False).elim
  | bigA _ => exact (hs : False).elim
  | a n =>
    by_cases hn : n.succ ∈ S
    · exact ⟨_, 1, small_mem M (s := .a n) trivial, one_mem _,
        (commute_x_block M j (s := .a n) hn rfl).symm, one_mem _, (mul_one _).symm⟩
    · exact ⟨(kLet M (.ta n) * (kLet M (.a n))⁻¹)⁻¹, kLet M (.ta n),
        inv_mem (mul_mem (small_mem M (s := .ta n) trivial)
          (inv_mem (small_mem M (s := .a n) trivial))),
        small_mem M (s := .ta n) trivial, (swap_a M j n S h0 hn).inv_left,
        block0_mem_centA M (s := .ta n) rfl, by group⟩
  | a' n =>
    by_cases hn : n.succ ∈ S
    · exact ⟨_, 1, small_mem M (s := .a' n) trivial, one_mem _,
        (commute_x_block M j (s := .a' n) hn rfl).symm, one_mem _, (mul_one _).symm⟩
    · exact ⟨(kLet M (.ta' n) * (kLet M (.a' n))⁻¹)⁻¹, kLet M (.ta' n),
        inv_mem (mul_mem (small_mem M (s := .ta' n) trivial)
          (inv_mem (small_mem M (s := .a' n) trivial))),
        small_mem M (s := .ta' n) trivial, (swap_a' M j n S h0 hn).inv_left,
        block0_mem_centA M (s := .ta' n) rfl, by group⟩
  | ta n => exact ⟨1, _, one_mem _, small_mem M (s := .ta n) trivial, Commute.one_left _,
      block0_mem_centA M (s := .ta n) rfl, (one_mul _).symm⟩
  | ta' n => exact ⟨1, _, one_mem _, small_mem M (s := .ta' n) trivial, Commute.one_left _,
      block0_mem_centA M (s := .ta' n) rfl, (one_mul _).symm⟩

/-- `x_{j,S}^g = x_{j,S}^p`, `p ∈ H_s ∩ ⟨a, a'⟩`, when `S` has no `A_{n+1}`. -/
theorem conj_C (j : Fin (N + 1)) {S : Finset (Fin (K + 1))} (hS : ∀ n : Fin K, n.succ ∉ S)
    {g : KhGroup M} (hg : g ∈ Subgroup.closure (smallSet M)) :
    ∃ p : KhGroup M, p ∈ Subgroup.closure (smallSet M) ∧ p ∈ aSub M ∧
      g⁻¹ * kLet M (.x j S) * g = p⁻¹ * kLet M (.x j S) * p :=
  conj_eq_of_dec (smallSet_comm M) _ (aSub M) (hdecC M j hS) hg

/-- `x_{j,S}^g = x_{j,S}^h`, `h ∈ H_s` commuting with all `A_{m+1}`, when `0 ∉ S`. -/
theorem conj_F (j : Fin (N + 1)) {S : Finset (Fin (K + 1))} (h0 : (0 : Fin (K + 1)) ∉ S)
    {g : KhGroup M} (hg : g ∈ Subgroup.closure (smallSet M)) :
    ∃ h : KhGroup M, h ∈ Subgroup.closure (smallSet M) ∧ h ∈ centA M ∧
      g⁻¹ * kLet M (.x j S) * g = h⁻¹ * kLet M (.x j S) * h :=
  conj_eq_of_dec (smallSet_comm M) _ (centA M) (hdecF M j h0) hg

end Sol

end KMS

end GroupApproximation.Full.Kharlampovich
