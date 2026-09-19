import GroupApproximation.ClassTransposition.Presentation.Gens

/-!
# The finitely presented group `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §3).

`H P` is presented by the finitely many generators `Gen P` and the relators of the bounded valid
instances of the families (a)–(d). In `H P`:
* the bounded valid instances hold (`inst_holds`);
* conjugation by the shift `s` moves a word one box to the right (`toH_up`);
* a word that never touches the tail does not depend on the level (`toH_stable`).
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-- The validity conditions of the instances. -/
def Inst.Valid (P : Set ℕ) : Inst → Prop
  | .sq n k => k + 2 ≤ n
  | .br n k => k + 3 ≤ n
  | .fsw n k l => k + 2 ≤ l ∧ l + 2 ≤ n
  | .fsp n i j p q => i < j ∧ j < n ∧ p ∈ P' P ∧ q ∈ P' P
  | .dl n k i p => i < k ∧ k + 2 ≤ n ∧ p ∈ P' P
  | .dr n k i p => k + 1 < i ∧ i < n ∧ p ∈ P' P
  | .dk n k p | .dk1 n k p => k + 2 ≤ n ∧ p ∈ P' P
  | .cx n i p q => i < n ∧ p ∈ P' P ∧ q ∈ P' P ∧ p ≠ q

/-- The size bound on the relators: every prime of `P ∪ {2}` plus a margin. -/
noncomputable def bnd (P : Set ℕ) : ℕ := sSup (P' P) + 20

/-- The relators of `H P`. -/
def rels (P : Set ℕ) : Set (FreeGroup (Gen P)) := relSet P (bnd P) (Inst.Valid P)

/-- The finitely presented group. -/
abbrev H (P : Set ℕ) : Type := PresentedGroup (rels P)

variable {P : Set ℕ}

/-- The generator of type `t` at position `j`, in `H P`. -/
def gH (t : Ty P) (j : ℕ) : H P := PresentedGroup.mk _ (gF t j)

/-- The shift in `H P`. -/
def sH (P : Set ℕ) : H P := PresentedGroup.mk _ (sF P)

/-- A word at level `n`, in `H P`. -/
noncomputable def toH (P : Set ℕ) (n : ℕ) (w : List Move) : H P :=
  PresentedGroup.mk _ (toFree P n w)

theorem toH_append (n : ℕ) (u v : List Move) :
    toH P n (u ++ v) = toH P n u * toH P (levW n u) v := by
  rw [toH, toFree_append, map_mul]; rfl

theorem gH_succ (t : Ty P) {j : ℕ} (hj : 2 ≤ j) : gH t (j + 1) = (sH P)⁻¹ * gH t j * sH P := by
  rw [gH, gF_succ t hj, map_mul, map_mul, map_inv]; rfl

theorem inst_holds {x : Inst} (hb : x.Bound (bnd P)) (hv : x.Valid P) :
    toH P x.lev x.sides.1 = toH P x.lev x.sides.2 :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨x, hb, hv, rfl⟩

/-! ### The shift moves words to the right -/

/-- A move one box further right. -/
def Move.up : Move → Move
  | .split i p => .split (i + 1) p
  | .swap k => .swap (k + 1)

/-- The move does not act on the first box. -/
def Move.Pos : Move → Prop
  | .split i _ => 1 ≤ i
  | .swap k => 1 ≤ k

theorem lev_up (m : Move) (n : ℕ) :
    m.up.lev (n + 1) = m.lev n + 1 := by
  cases m with
  | split i p =>
    simp only [Move.up, Move.lev]
    by_cases h : i < n
    · rw [if_pos h, if_pos (by omega)]
      omega
    · rw [if_neg h, if_neg (by omega)]
  | swap k => rfl

theorem hatF_up (m : Move) (hm : m.Pos) (n : ℕ) :
    hatF P m.up (n + 1) = (sF P)⁻¹ * hatF P m n * sF P := by
  cases m with
  | split i p =>
    simp only [Move.Pos] at hm
    simp only [Move.up, hatF]
    by_cases h1 : i + 1 < n
    · rw [if_pos (by omega), if_pos h1]
      split_ifs
      · exact gF_succ _ (by omega)
      · group
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : i + 1 = n ∧ p ≠ 2
      · rw [if_pos (by omega), if_pos h2]
        split_ifs
        · exact gF_succ _ (by omega)
        · group
      · rw [if_neg (by omega), if_neg h2]
        group
  | swap k =>
    simp only [Move.Pos] at hm
    simp only [Move.up, hatF]
    by_cases h1 : k + 2 < n
    · rw [if_pos (by omega), if_pos h1]
      exact gF_succ _ (by omega)
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : k + 2 = n
      · rw [if_pos (by omega), if_pos h2]
        exact gF_succ _ (by omega)
      · rw [if_neg (by omega), if_neg h2]
        group

/-- Conjugation by the shift moves a word one box to the right. -/
theorem toFree_up : ∀ (w : List Move), (∀ m ∈ w, m.Pos) → ∀ n,
    toFree P (n + 1) (w.map Move.up) = (sF P)⁻¹ * toFree P n w * sF P
  | [], _, _ => by simp
  | m :: w, hw, n => by
    rw [List.map_cons, toFree_cons, toFree_cons, lev_up, hatF_up m (hw m List.mem_cons_self),
      toFree_up w (fun m' hm' => hw m' (List.mem_cons_of_mem _ hm'))]
    group

theorem toH_up (w : List Move) (hw : ∀ m ∈ w, m.Pos) (n : ℕ) :
    toH P (n + 1) (w.map Move.up) = (sH P)⁻¹ * toH P n w * sH P := by
  rw [toH, toFree_up w hw, map_mul, map_mul, map_inv]; rfl

theorem levW_up : ∀ (w : List Move) (n : ℕ), levW (n + 1) (w.map Move.up) = levW n w + 1
  | [], _ => rfl
  | m :: w, n => by rw [List.map_cons, levW_cons, levW_cons, lev_up, levW_up w]

/-! ### Words away from the tail do not depend on the level -/

/-- The move acts on a box before the tail of a list of `n` boxes. -/
def Move.Front : Move → ℕ → Prop
  | .split i _, n => i + 1 < n
  | .swap k, n => k + 2 < n

/-- Every move of the word acts before the tail. -/
def FrontW : ℕ → List Move → Prop
  | _, [] => True
  | n, m :: w => m.Front n ∧ FrontW (m.lev n) w

theorem hatF_stable (m : Move) (n : ℕ) (h : m.Front n) : hatF P m (n + 1) = hatF P m n := by
  cases m with
  | split i p =>
    simp only [Move.Front] at h
    simp only [hatF]
    rw [if_pos h, if_pos (by omega)]
  | swap k =>
    simp only [Move.Front] at h
    simp only [hatF]
    rw [if_pos h, if_pos (by omega)]

theorem lev_stable (m : Move) (n : ℕ) (h : m.Front n) : m.lev (n + 1) = m.lev n + 1 := by
  cases m with
  | split i p =>
    simp only [Move.Front] at h
    simp only [Move.lev]
    rw [if_pos (by omega), if_pos (by omega)]
    omega
  | swap k => rfl

theorem front_stable : ∀ (w : List Move) (n : ℕ), FrontW n w → FrontW (n + 1) w
  | [], _, _ => trivial
  | m :: w, n, ⟨h1, h2⟩ => by
    refine ⟨?_, ?_⟩
    · cases m with
      | split i p => simp only [Move.Front] at h1 ⊢; omega
      | swap k => simp only [Move.Front] at h1 ⊢; omega
    · rw [lev_stable m n h1]; exact front_stable w _ h2

theorem toFree_stable : ∀ (w : List Move) (n : ℕ), FrontW n w →
    toFree P (n + 1) w = toFree P n w
  | [], _, _ => rfl
  | m :: w, n, ⟨h1, h2⟩ => by
    rw [toFree_cons, toFree_cons, hatF_stable m n h1, lev_stable m n h1,
      toFree_stable w _ h2]

theorem toH_stable (w : List Move) (n : ℕ) (h : FrontW n w) : toH P (n + 1) w = toH P n w := by
  rw [toH, toH, toFree_stable w n h]

end GroupApproximation.ClassTransposition.Presentation
