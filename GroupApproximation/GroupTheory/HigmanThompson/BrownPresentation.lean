import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group
import GroupApproximation.GroupTheory.HigmanThompson.Generators
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's finite presentation of `F_{m+2,∞}`

The group `BrownGroup m` is presented on `x_0, …, x_{m+1}` by the finitely many relators
`X_i X_j X_i⁻¹ X_{j+m+1}⁻¹` with `1 ≤ i ≤ m + 1` and `i < j ≤ i + m + 2`, where the words
`X_k` for `k ≥ m + 2` are defined by `X_k = x_0 X_{k-m-1} x_0⁻¹`.

* `brownX_rel`: every relation `X_i X_j X_i⁻¹ = X_{j+m+1}`, `i < j`, follows (strong induction
  on `j - i`; the long relations reduce to shorter ones through `X_{i+1}`, and relations at
  large `i` are `x_0`-conjugates of relations at smaller `i`).
* `brownEval_injective`: the evaluation `x_k ↦ xg m k` into `Equiv.Perm ℚ` is injective.
  Every element is `p⁻¹ · q` with `p, q` positive (`exists_form`), positive words sort by
  insertion (`brownPos_brownSort`), and a sorted positive word is read off its evaluation:
  its first letter `a` is where the map first moves points (`x_k` fixes `(-∞, k]` and
  moves `(a, a+1]` up), so two sorted words with equal evaluations agree letter by letter
  (`sorted_eq_of_eval_eq`).
* `brownF_isFinitelyPresented`: the image group is finitely presented.
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m : ℕ)

/-- The word `X_k` in the free group on `x_0, …, x_{m+1}`. -/
def brownWord (k : ℕ) : FreeGroup (Fin (m + 2)) :=
  if h : k < m + 2 then FreeGroup.of ⟨k, h⟩ else
    FreeGroup.of ⟨0, by omega⟩ * brownWord (k - (m + 1)) * (FreeGroup.of ⟨0, by omega⟩)⁻¹
termination_by k
decreasing_by omega

theorem brownWord_of_lt {k : ℕ} (h : k < m + 2) : brownWord m k = FreeGroup.of ⟨k, h⟩ := by
  rw [brownWord, dif_pos h]

theorem brownWord_of_ge {k : ℕ} (h : m + 2 ≤ k) :
    brownWord m k = FreeGroup.of ⟨0, by omega⟩ * brownWord m (k - (m + 1)) *
      (FreeGroup.of ⟨0, by omega⟩)⁻¹ := by
  rw [brownWord, dif_neg (by omega)]

/-- Brown's finitely many relators. -/
def brownRels : Set (FreeGroup (Fin (m + 2))) :=
  {r | ∃ i j : ℕ, 1 ≤ i ∧ i ≤ m + 1 ∧ i < j ∧ j ≤ i + m + 2 ∧
    r = brownWord m i * brownWord m j * (brownWord m i)⁻¹ * (brownWord m (j + m + 1))⁻¹}

theorem brownRels_finite : (brownRels m).Finite := by
  have hsub : brownRels m ⊆ (fun p : ℕ × ℕ => brownWord m p.1 * brownWord m p.2 *
      (brownWord m p.1)⁻¹ * (brownWord m (p.2 + m + 1))⁻¹) ''
        ((Finset.range (m + 2) ×ˢ Finset.range (2 * m + 4) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro r ⟨i, j, h1, h2, h3, h4, rfl⟩
    refine ⟨(i, j), ?_, rfl⟩
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    omega
  exact ((Finset.finite_toSet _).image _).subset hsub

/-- Brown's group. -/
abbrev BrownGroup := PresentedGroup (brownRels m)

/-- `X_k` in Brown's group. -/
def brownX (k : ℕ) : BrownGroup m := PresentedGroup.mk (brownRels m) (brownWord m k)

theorem brownX_of_ge {k : ℕ} (h : m + 2 ≤ k) :
    brownX m k = brownX m 0 * brownX m (k - (m + 1)) * (brownX m 0)⁻¹ := by
  have h0 : brownWord m 0 = FreeGroup.of ⟨0, by omega⟩ := brownWord_of_lt m (by omega)
  rw [brownX, brownWord_of_ge m h, map_mul, map_mul, map_inv, brownX, brownX, h0]

/-! ## All of Brown's relations -/

theorem brownX_rel_short {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m + 1) (h3 : i < j)
    (h4 : j ≤ i + m + 2) :
    brownX m i * brownX m j * (brownX m i)⁻¹ = brownX m (j + m + 1) := by
  have hr : PresentedGroup.mk (brownRels m) (brownWord m i * brownWord m j * (brownWord m i)⁻¹ *
      (brownWord m (j + m + 1))⁻¹) = 1 := PresentedGroup.one_of_mem ⟨i, j, h1, h2, h3, h4, rfl⟩
  simp only [map_mul, map_inv] at hr
  exact mul_inv_eq_one.mp hr

theorem brownX_rel_zero {j : ℕ} (hj : 1 ≤ j) :
    brownX m 0 * brownX m j * (brownX m 0)⁻¹ = brownX m (j + m + 1) := by
  rw [brownX_of_ge m (show m + 2 ≤ j + m + 1 by omega), show j + m + 1 - (m + 1) = j by omega]

theorem brownX_rel_all (d : ℕ) : ∀ i j : ℕ, j = i + d + 1 →
    brownX m i * brownX m j * (brownX m i)⁻¹ = brownX m (j + m + 1) := by
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro i
    by_cases hd : d + 1 ≤ m + 2
    · induction i using Nat.strong_induction_on with
      | _ i ihi =>
        intro j hj
        by_cases hi0 : i = 0
        · subst hi0
          exact brownX_rel_zero m (by omega)
        by_cases hi : i ≤ m + 1
        · exact brownX_rel_short m (by omega) hi (by omega) (by omega)
        · have hi' : m + 2 ≤ i := by omega
          have key := ihi (i - (m + 1)) (by omega) (j - (m + 1)) (by omega)
          rw [brownX_of_ge m hi', brownX_of_ge m (show m + 2 ≤ j by omega),
            brownX_of_ge m (show m + 2 ≤ j + m + 1 by omega),
            show j + m + 1 - (m + 1) = j - (m + 1) + m + 1 by omega, ← key]
          group
    · intro j hj
      have hd' : m + 2 ≤ d := by omega
      have r1 := ihd (d - (m + 2)) (by omega) (i + 1) (i + (d - (m + 1)) + 1) (by omega)
      rw [show i + (d - (m + 1)) + 1 + m + 1 = j by omega] at r1
      have r2 := ihd 0 (by omega) i (i + 1) (by omega)
      have r3 := ihd (d - (m + 1)) (by omega) i (i + (d - (m + 1)) + 1) (by omega)
      have r4 := ihd (d - (m + 2)) (by omega) (i + 1 + m + 1)
        (i + (d - (m + 1)) + 1 + m + 1) (by omega)
      rw [show i + (d - (m + 1)) + 1 + m + 1 + m + 1 = j + m + 1 by omega] at r4
      calc brownX m i * brownX m j * (brownX m i)⁻¹
          = brownX m i * (brownX m (i + 1) * brownX m (i + (d - (m + 1)) + 1) *
              (brownX m (i + 1))⁻¹) * (brownX m i)⁻¹ := by rw [r1]
        _ = (brownX m i * brownX m (i + 1) * (brownX m i)⁻¹) *
              (brownX m i * brownX m (i + (d - (m + 1)) + 1) * (brownX m i)⁻¹) *
              (brownX m i * brownX m (i + 1) * (brownX m i)⁻¹)⁻¹ := by group
        _ = brownX m (i + 1 + m + 1) * brownX m (i + (d - (m + 1)) + 1 + m + 1) *
              (brownX m (i + 1 + m + 1))⁻¹ := by rw [r2, r3]
        _ = brownX m (j + m + 1) := r4

/-- **Brown's relations**: `X_i X_j X_i⁻¹ = X_{j+m+1}` for all `i < j`. -/
theorem brownX_rel {i j : ℕ} (h : i < j) :
    brownX m i * brownX m j * (brownX m i)⁻¹ = brownX m (j + m + 1) :=
  brownX_rel_all m (j - i - 1) i j (by omega)

/-! ## Positive words and normal forms -/

/-- A positive word, head applied first: `brownPos [i₁, …, i_k] = X_{i_k} ⋯ X_{i₁}`. -/
def brownPos : List ℕ → BrownGroup m
  | [] => 1
  | i :: l => brownPos l * brownX m i

theorem brownPos_append (l₁ l₂ : List ℕ) :
    brownPos m (l₁ ++ l₂) = brownPos m l₂ * brownPos m l₁ := by
  induction l₁ with
  | nil => simp [brownPos]
  | cons i l ih => simp only [List.cons_append, brownPos, ih, mul_assoc]

theorem brown_move (q : List ℕ) : ∀ k : ℕ, ∃ q' p' : List ℕ,
    brownX m k * (brownPos m q)⁻¹ = (brownPos m q')⁻¹ * brownPos m p' := by
  induction q with
  | nil => exact fun k => ⟨[], [k], by simp [brownPos]⟩
  | cons j q ih =>
    intro k
    rcases lt_trichotomy k j with hkj | rfl | hkj
    · obtain ⟨q', p', h⟩ := ih k
      refine ⟨(j + m + 1) :: q', p', ?_⟩
      have hr : brownX m k * (brownX m j)⁻¹ = (brownX m (j + m + 1))⁻¹ * brownX m k := by
        rw [← brownX_rel m hkj]
        group
      calc brownX m k * (brownPos m (j :: q))⁻¹
          = brownX m k * (brownX m j)⁻¹ * (brownPos m q)⁻¹ := by
            simp only [brownPos, mul_inv_rev, mul_assoc]
        _ = (brownX m (j + m + 1))⁻¹ * (brownX m k * (brownPos m q)⁻¹) := by
            rw [hr, mul_assoc]
        _ = (brownX m (j + m + 1))⁻¹ * ((brownPos m q')⁻¹ * brownPos m p') := by rw [h]
        _ = (brownPos m ((j + m + 1) :: q'))⁻¹ * brownPos m p' := by
            simp only [brownPos, mul_inv_rev, mul_assoc]
    · exact ⟨q, [], by simp [brownPos]⟩
    · obtain ⟨q', p', h⟩ := ih (k + m + 1)
      refine ⟨j :: q', p', ?_⟩
      have hr : brownX m k * (brownX m j)⁻¹ = (brownX m j)⁻¹ * brownX m (k + m + 1) := by
        rw [← brownX_rel m hkj]
        group
      calc brownX m k * (brownPos m (j :: q))⁻¹
          = brownX m k * (brownX m j)⁻¹ * (brownPos m q)⁻¹ := by
            simp only [brownPos, mul_inv_rev, mul_assoc]
        _ = (brownX m j)⁻¹ * (brownX m (k + m + 1) * (brownPos m q)⁻¹) := by
            rw [hr, mul_assoc]
        _ = (brownX m j)⁻¹ * ((brownPos m q')⁻¹ * brownPos m p') := by rw [h]
        _ = (brownPos m (j :: q'))⁻¹ * brownPos m p' := by
            simp only [brownPos, mul_inv_rev, mul_assoc]

theorem brownX_of_fin (x : Fin (m + 2)) :
    PresentedGroup.mk (brownRels m) (FreeGroup.of x) = brownX m x.val := by
  rw [brownX, brownWord_of_lt m x.isLt]

/-- **Every element is `p⁻¹ q` with `p, q` positive.** -/
theorem exists_form (g : BrownGroup m) : ∃ q p : List ℕ, g = (brownPos m q)⁻¹ * brownPos m p := by
  have key : ∀ w : FreeGroup (Fin (m + 2)), ∀ q p : List ℕ, ∃ q' p' : List ℕ,
      PresentedGroup.mk (brownRels m) w * ((brownPos m q)⁻¹ * brownPos m p) =
        (brownPos m q')⁻¹ * brownPos m p' := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 => exact fun q p => ⟨q, p, by simp⟩
    | of x =>
        intro q p
        obtain ⟨q', p', h⟩ := brown_move m q x.val
        refine ⟨q', p ++ p', ?_⟩
        rw [brownX_of_fin, ← mul_assoc, h, mul_assoc, brownPos_append]
    | inv_of x _ =>
        intro q p
        refine ⟨x.val :: q, p, ?_⟩
        rw [map_inv, brownX_of_fin]
        simp only [brownPos, mul_inv_rev, mul_assoc]
    | mul x y ihx ihy =>
        intro q p
        obtain ⟨q₁, p₁, h₁⟩ := ihy q p
        obtain ⟨q₂, p₂, h₂⟩ := ihx q₁ p₁
        exact ⟨q₂, p₂, by rw [map_mul, mul_assoc, h₁, h₂]⟩
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (brownRels m) g
  obtain ⟨q, p, h⟩ := key w [] []
  exact ⟨q, p, by simpa [brownPos] using h⟩

/-! ## Sorting positive words -/

/-- Insert a letter applied first, keeping the word sorted. -/
def brownIns (j : ℕ) : List ℕ → List ℕ
  | [] => [j]
  | i :: l => if j ≤ i then j :: i :: l else i :: brownIns (j + m + 1) l

theorem brownPos_brownIns (l : List ℕ) : ∀ j : ℕ,
    brownPos m (brownIns m j l) = brownPos m (j :: l) := by
  induction l with
  | nil => exact fun j => rfl
  | cons i l ih =>
    intro j
    by_cases h : j ≤ i
    · simp only [brownIns, if_pos h]
    · simp only [brownIns, if_neg h, brownPos, ih]
      have hr : brownX m i * brownX m j = brownX m (j + m + 1) * brownX m i := by
        rw [← brownX_rel m (not_le.mp h)]
        group
      rw [mul_assoc, ← hr, ← mul_assoc]

theorem mem_brownIns {j x : ℕ} {l : List ℕ} (hx : x ∈ brownIns m j l) : j ≤ x ∨ x ∈ l := by
  induction l generalizing j with
  | nil =>
    simp only [brownIns, List.mem_singleton] at hx
    exact Or.inl hx.ge
  | cons i l ih =>
    by_cases h : j ≤ i
    · simp only [brownIns, if_pos h, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl le_rfl
      · exact Or.inr (List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ hx)
    · simp only [brownIns, if_neg h, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr List.mem_cons_self
      · rcases ih hx with h1 | h1
        · exact Or.inl (by omega)
        · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem brownIns_sorted {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) :
    ∀ j : ℕ, (brownIns m j l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => exact fun j => List.pairwise_singleton _ _
  | cons i l ih =>
    intro j
    have hl' := List.pairwise_cons.mp hl
    by_cases h : j ≤ i
    · simp only [brownIns, if_pos h]
      refine List.pairwise_cons.mpr ⟨?_, hl⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h
      · exact le_trans h (hl'.1 x hx)
    · simp only [brownIns, if_neg h]
      refine List.pairwise_cons.mpr ⟨?_, ih hl'.2 _⟩
      intro x hx
      rcases mem_brownIns m hx with h1 | h1
      · omega
      · exact hl'.1 x h1

/-- Insertion sort of positive words. -/
def brownSort : List ℕ → List ℕ
  | [] => []
  | j :: l => brownIns m j (brownSort l)

theorem brownPos_brownSort (l : List ℕ) : brownPos m (brownSort m l) = brownPos m l := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [brownSort, brownPos_brownIns, brownPos, ih]

theorem brownSort_sorted (l : List ℕ) : (brownSort m l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons j l ih => exact brownIns_sorted m ih j

/-! ## Evaluation -/

theorem lift_brownWord (k : ℕ) :
    FreeGroup.lift (fun i : Fin (m + 2) => xg m i.val) (brownWord m k) = xg m k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k < m + 2
    · rw [brownWord_of_lt m h, FreeGroup.lift_apply_of]
    · rw [brownWord_of_ge m (not_lt.mp h), map_mul, map_mul, map_inv, FreeGroup.lift_apply_of,
        ih (k - (m + 1)) (by omega)]
      have hcomm := xg_comm (m := m) (show 0 < k - (m + 1) by omega)
      rw [show k - (m + 1) + m + 1 = k by omega] at hcomm
      rw [hcomm, mul_inv_cancel_right]

theorem brownRels_eval :
    ∀ r ∈ brownRels m, FreeGroup.lift (fun i : Fin (m + 2) => xg m i.val) r = 1 := by
  rintro r ⟨i, j, -, -, hij, -, rfl⟩
  simp only [map_mul, map_inv, lift_brownWord]
  rw [xg_comm hij]
  group

/-- The evaluation of Brown's group into `Equiv.Perm ℚ`. -/
noncomputable def brownEval : BrownGroup m →* Equiv.Perm ℚ :=
  PresentedGroup.toGroup (brownRels_eval m)

theorem brownEval_X (k : ℕ) : brownEval m (brownX m k) = xg m k :=
  lift_brownWord m k

theorem brownEval_pos_cons (i : ℕ) (l : List ℕ) :
    brownEval m (brownPos m (i :: l)) = brownEval m (brownPos m l) * xg m i := by
  rw [brownPos, map_mul, brownEval_X]

theorem brownEval_pos_fix {b : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, b ≤ x) {t : ℚ} (ht : t ≤ b) :
    brownEval m (brownPos m l) t = t := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [brownEval_pos_cons, Equiv.Perm.mul_apply,
      xg_fix (show t ≤ (i : ℚ) from le_trans ht (by exact_mod_cast hl i List.mem_cons_self))]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem le_brownEval_pos (l : List ℕ) (t : ℚ) : t ≤ brownEval m (brownPos m l) t := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons i l ih =>
    rw [brownEval_pos_cons, Equiv.Perm.mul_apply]
    exact le_trans (le_xg i t) (ih _)

theorem lt_brownEval_pos_cons (a : ℕ) (l : List ℕ) {t : ℚ} (ht : (a : ℚ) < t) :
    t < brownEval m (brownPos m (a :: l)) t := by
  rw [brownEval_pos_cons, Equiv.Perm.mul_apply]
  exact lt_of_lt_of_le (lt_xg_of_mem ht) (le_brownEval_pos m l _)

/-- **Sorted positive words are determined by their evaluation.** -/
theorem sorted_eq_of_eval_eq (p : List ℕ) : ∀ q : List ℕ, p.Pairwise (· ≤ ·) →
    q.Pairwise (· ≤ ·) → brownEval m (brownPos m p) = brownEval m (brownPos m q) → p = q := by
  induction p with
  | nil =>
    intro q _ _ h
    rcases q with _ | ⟨b, q⟩
    · rfl
    · exfalso
      have h1 := lt_brownEval_pos_cons m b q (show (b : ℚ) < b + 1 by linarith)
      rw [← h] at h1
      simp [brownPos] at h1
  | cons a p ih =>
    intro q hp hq h
    rcases q with _ | ⟨b, q⟩
    · exfalso
      have h1 := lt_brownEval_pos_cons m a p (show (a : ℚ) < a + 1 by linarith)
      rw [h] at h1
      simp [brownPos] at h1
    have hp' := List.pairwise_cons.mp hp
    have hq' := List.pairwise_cons.mp hq
    rcases lt_trichotomy a b with hab | rfl | hab
    · exfalso
      have hab' : (a : ℚ) + 1 ≤ b := by
        have : a + 1 ≤ b := hab
        exact_mod_cast this
      have h1 := lt_brownEval_pos_cons m a p (show (a : ℚ) < a + 1 by linarith)
      have h2 : brownEval m (brownPos m (b :: q)) ((a : ℚ) + 1) = (a : ℚ) + 1 :=
        brownEval_pos_fix m (b := b)
          (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_rfl
            · exact hq'.1 x hx) hab'
      rw [h, h2] at h1
      exact lt_irrefl _ h1
    · have hcancel : brownEval m (brownPos m p) = brownEval m (brownPos m q) := by
        have h' := h
        rw [brownEval_pos_cons, brownEval_pos_cons] at h'
        exact mul_right_cancel h'
      rw [ih q hp'.2 hq'.2 hcancel]
    · exfalso
      have hab' : (b : ℚ) + 1 ≤ a := by
        have : b + 1 ≤ a := hab
        exact_mod_cast this
      have h1 := lt_brownEval_pos_cons m b q (show (b : ℚ) < b + 1 by linarith)
      have h2 : brownEval m (brownPos m (a :: p)) ((b : ℚ) + 1) = (b : ℚ) + 1 :=
        brownEval_pos_fix m (b := a)
          (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact le_rfl
            · exact hp'.1 x hx) hab'
      rw [← h, h2] at h1
      exact lt_irrefl _ h1

/-- **The evaluation of Brown's group is injective.** -/
theorem brownEval_injective : Function.Injective (brownEval m) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨q, p, rfl⟩ := exists_form m g
  have h1 : brownEval m (brownPos m p) = brownEval m (brownPos m q) := by
    rw [map_mul, map_inv, inv_mul_eq_one] at hg
    exact hg.symm
  have h2 : brownEval m (brownPos m (brownSort m p)) = brownEval m (brownPos m (brownSort m q)) := by
    rw [brownPos_brownSort, brownPos_brownSort, h1]
  have h3 := sorted_eq_of_eval_eq m _ _ (brownSort_sorted m p) (brownSort_sorted m q) h2
  have h4 : brownPos m p = brownPos m q := by
    rw [← brownPos_brownSort m p, h3, brownPos_brownSort]
  rw [h4, inv_mul_cancel]

/-- The subgroup of `Equiv.Perm ℚ` generated by the `x_k`: Brown's `F_{m+2,∞}`. -/
noncomputable def brownF : Subgroup (Equiv.Perm ℚ) := (brownEval m).range

theorem xg_mem_brownF (k : ℕ) : xg m k ∈ brownF m := ⟨brownX m k, brownEval_X m k⟩

/-- **`F_{m+2,∞}` is finitely presented.** -/
theorem brownF_isFinitelyPresented : Group.IsFinitelyPresented (brownF m) := by
  haveI : Finite (brownRels m) := (brownRels_finite m).to_subtype
  exact Group.IsFinitelyPresented.equiv (MonoidHom.ofInjective (brownEval_injective m))

#audit_axioms GroupApproximation.HigmanThompson.brownEval_injective
#audit_axioms GroupApproximation.HigmanThompson.brownF_isFinitelyPresented

end HigmanThompson
end GroupApproximation
