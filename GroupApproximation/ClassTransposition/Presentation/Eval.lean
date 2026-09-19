import GroupApproximation.ClassTransposition.Presentation.Conc
import GroupApproximation.ClassTransposition.Presentation.Hats

/-!
# Evaluating the generators and words of `H P`

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`, §1).

* `evGen`: each generator evaluates to the concrete element of its move at its minimal level.
* `lift_gF`: the shift definitions evaluate correctly at every position, by `conc_up`.
* `lift_hatF`: a valid move at any level evaluates to its concrete element.
* `lift_toFree`: a valid word evaluates to `frac` of the comb onto its realization.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

/-! ### The shift -/

theorem up_app {m : Move} (hm : m.Pos) (b : List Box) :
    splitAt (m.app b) 0 2 = m.up.app (splitAt b 0 2) := by
  cases m with
  | split i p =>
    simp only [Move.Pos] at hm
    show splitAt (splitAt b i p) 0 2 = splitAt (splitAt b 0 2) (i + 1) p
    rw [← splitAt_splitAt_far 2 b 0 i p (by omega)]
  | swap k =>
    simp only [Move.Pos] at hm
    show splitAt (swapAt b k) 0 2 = swapAt (splitAt b 0 2) (k + 1)
    rw [splitAt_swapAt_left 2 b k 0 (by omega)]

theorem lev_split02 {N : ℕ} (hN : 0 < N) : (Move.split 0 2).lev N = N + 1 := by
  rw [lev_split 2 hN]; omega

/-- **Shift.** Conjugating by the concrete shift moves a concrete element one box right. -/
theorem conc_up {m : Move} (hm : m.Pos) (hm0 : m.Ok) {n : ℕ} (hn : 0 < n) :
    conc m.up (n + 1) = (conc (.split 0 2) n)⁻¹ * conc m n * conc (.split 0 2) (m.lev n) := by
  have hL := lev_pos hn hm0
  have p1 : IsPart (comb (m.lev n + 1)) := isPart_comb _ (by omega)
  have p2 : IsPart (splitAt (comb (m.lev n)) 0 2) := isPart_splitAt (isPart_comb _ hL) 0 (by norm_num)
  have p3 : IsPart (m.app (comb n)) := isPart_comb_app hn hm0
  have p4 : IsPart (splitAt (comb n) 0 2) := isPart_splitAt (isPart_comb _ hn) 0 (by norm_num)
  have p5 : IsPart (comb (n + 1)) := isPart_comb _ (by omega)
  have hup : m.up.Ok := by cases m <;> exact hm0
  have p6 : IsPart (m.up.app (comb (n + 1))) := isPart_app p5 hup
  have e1 : conc (.split 0 2) (m.lev n) =
      frac (comb (m.lev n + 1)) (splitAt (comb (m.lev n)) 0 2) := by
    show frac (comb ((Move.split 0 2).lev (m.lev n))) (splitAt (comb (m.lev n)) 0 2) = _
    rw [lev_split02 hL]
  have e2 : conc (.split 0 2) n = frac (comb (n + 1)) (splitAt (comb n) 0 2) := by
    show frac (comb ((Move.split 0 2).lev n)) (splitAt (comb n) 0 2) = _
    rw [lev_split02 hn]
  have l1 : (comb (m.lev n + 1)).length = (splitAt (comb (m.lev n)) 0 2).length := by
    rw [length_splitAt (comb (m.lev n)) 0 2 (by rw [length_comb]; exact hL), length_comb,
      length_comb]; omega
  have l2 : (comb (m.lev n)).length = (m.app (comb n)).length := by
    rw [length_app, length_comb, length_comb]
  have l3 : (comb (n + 1)).length = (splitAt (comb n) 0 2).length := by
    rw [length_splitAt (comb n) 0 2 (by rw [length_comb]; exact hn), length_comb, length_comb]
    omega
  have h1 := frac_canon p1 p2 l1
  have h2 := forall₂_splitAt (frac_canon (isPart_comb _ hL) p3 l2) 0 2
  have h3 := forall₂_app (forall₂_canon_inv (frac_canon p5 p4 l3)) m.up
  rw [← up_app hm] at h3
  have h := forall₂_canon_comp (forall₂_canon_comp h1 h2) h3
  rw [e1, e2, conc, lev_up, ← eq_frac p1 p6 h]
  unfold conc
  group

/-- The concrete shift does not depend on the level. -/
theorem conc_split02 : ∀ N, 2 ≤ N → conc (.split 0 2) N = conc (.split 0 2) 2
  | 0, h => absurd h (by norm_num)
  | 1, h => absurd h (by norm_num)
  | 2, _ => rfl
  | N + 3, _ => by
    show conc (.split 0 2) (N + 2 + 1) = _
    rw [conc_stable (m := .split 0 2) (n := N + 2) (by omega) (show 0 + 1 < N + 2 by omega)
        (show 0 < 2 by norm_num),
      conc_split02 (N + 2) (by omega)]

/-- A move before the tail has the same concrete element at every higher level. -/
theorem conc_stable_to {m : Move} (hm0 : m.Ok) {N : ℕ} (hN : 0 < N) (hm : m.Front N) :
    ∀ n, N ≤ n → conc m n = conc m N := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hf : m.Front n := by
      cases m with
      | split i p => simp only [Move.Front] at hm ⊢; omega
      | swap k => simp only [Move.Front] at hm ⊢; omega
    rw [conc_stable (by omega) hf hm0, ih]

/-! ### The generators -/

variable {P : Set ℕ}

/-- The move of a generator type at position `j`. -/
def moveT : Ty P → ℕ → Move
  | Sum.inl p, j => .split (j - 1) p.1
  | Sum.inr (Sum.inl p), j => .split (j - 1) p.1
  | Sum.inr (Sum.inr _), j => .swap (j - 1)

/-- The minimal level of a generator type at position `j`. -/
def levT : Ty P → ℕ → ℕ
  | Sum.inl _, j => j + 1
  | Sum.inr (Sum.inl _), j => j
  | Sum.inr (Sum.inr false), j => j + 2
  | Sum.inr (Sum.inr true), j => j + 1

/-- The concrete element of a generator type at position `j`. -/
noncomputable def concT (t : Ty P) (j : ℕ) : Perm ℤ := conc (moveT t j) (levT t j)

/-- The evaluation of the finitely many generators. -/
noncomputable def evGen (x : Gen P) : Perm ℤ := concT x.1 (if x.2 then 2 else 1)

theorem moveT_succ (t : Ty P) {j : ℕ} (hj : 1 ≤ j) : moveT t (j + 1) = (moveT t j).up := by
  rcases t with _ | _ | _ <;> (simp only [moveT, Move.up]; congr 1; omega)

theorem levT_succ (t : Ty P) (j : ℕ) : levT t (j + 1) = levT t j + 1 := by
  rcases t with _ | _ | b
  · rfl
  · rfl
  · cases b <;> rfl

theorem levT_ge (t : Ty P) (j : ℕ) : j ≤ levT t j := by
  rcases t with _ | _ | b
  · show j ≤ j + 1; omega
  · exact le_refl j
  · cases b
    · show j ≤ j + 2; omega
    · show j ≤ j + 1; omega

theorem moveT_ok (hpos : ∀ p ∈ P' P, 2 ≤ p) (t : Ty P) (j : ℕ) : (moveT t j).Ok := by
  rcases t with ⟨p, hp⟩ | ⟨p, hp⟩ | _
  · show 0 < p; have := hpos p hp; omega
  · show 0 < p; have := hpos p (Set.mem_insert_of_mem _ hp); omega
  · trivial

theorem moveT_pos (t : Ty P) {j : ℕ} (hj : 2 ≤ j) : (moveT t j).Pos := by
  rcases t with _ | _ | _
  · show 1 ≤ j - 1; omega
  · show 1 ≤ j - 1; omega
  · show 1 ≤ j - 1; omega

theorem lev_ge {m : Move} (hm : m.Ok) (n : ℕ) : n ≤ m.lev n := by
  cases m with
  | split i p =>
    simp only [Move.Ok] at hm
    simp only [Move.lev]
    split_ifs <;> omega
  | swap k => exact le_refl n

theorem lift_sF : FreeGroup.lift (evGen (P := P)) (sF P) = conc (.split 0 2) 2 :=
  FreeGroup.lift_apply_of

/-- The shift definitions evaluate to the concrete elements at every position. -/
theorem lift_gF (hpos : ∀ p ∈ P' P, 2 ≤ p) (t : Ty P) :
    ∀ j, 1 ≤ j → FreeGroup.lift (evGen (P := P)) (gF t j) = concT t j
  | 0, h => absurd h (by norm_num)
  | 1, _ => FreeGroup.lift_apply_of
  | 2, _ => FreeGroup.lift_apply_of
  | j + 3, _ => by
    have ih := lift_gF hpos t (j + 2) (by omega)
    have hn : 2 ≤ levT t (j + 2) := by have := levT_ge t (j + 2); omega
    have hL : 2 ≤ (moveT t (j + 2)).lev (levT t (j + 2)) :=
      hn.trans (lev_ge (moveT_ok hpos t _) _)
    have key : concT t (j + 3) =
        (conc (.split 0 2) 2)⁻¹ * concT t (j + 2) * conc (.split 0 2) 2 := by
      show conc (moveT t (j + 2 + 1)) (levT t (j + 2 + 1)) =
        (conc (.split 0 2) 2)⁻¹ * conc (moveT t (j + 2)) (levT t (j + 2)) * conc (.split 0 2) 2
      rw [moveT_succ t (by omega), levT_succ,
        conc_up (moveT_pos t (by omega)) (moveT_ok hpos t _) (by omega),
        conc_split02 _ hn, conc_split02 _ hL]
    rw [key, gF, map_mul, map_mul, map_inv, ih, lift_sF]

/-! ### Moves and words -/

/-- A move is valid at level `n`: it acts on an existing box, and splits by a prime of
`P ∪ {2}`. -/
def Move.Val (P : Set ℕ) : Move → ℕ → Prop
  | .split i p, n => i < n ∧ p ∈ P' P
  | .swap k, n => k + 1 < n

/-- Every move of the word is valid at its level. -/
def ValW (P : Set ℕ) : ℕ → List Move → Prop
  | _, [] => True
  | n, m :: w => m.Val P n ∧ ValW P (m.lev n) w

theorem Move.Val.ok (hpos : ∀ p ∈ P' P, 2 ≤ p) {m : Move} {n : ℕ} (h : m.Val P n) : m.Ok := by
  cases m with
  | split i p => have := hpos p h.2; show 0 < p; omega
  | swap k => trivial

theorem conc_tail_two {n : ℕ} (hn : 0 < n) : conc (.split (n - 1) 2) n = 1 := by
  show frac (comb ((Move.split (n - 1) 2).lev n)) (splitAt (comb n) (n - 1) 2) = 1
  rw [lev_split 2 (by omega), ← comb_succ_tail hn, show n + 2 - 1 = n + 1 by omega,
    frac_self (isPart_comb _ (by omega))]

theorem ValW.ok (hpos : ∀ p ∈ P' P, 2 ≤ p) : ∀ {n : ℕ} {w : List Move}, ValW P n w →
    ∀ m ∈ w, m.Ok
  | _, [], _, _, h => absurd h List.not_mem_nil
  | _, m :: w, ⟨hm, hw⟩, m', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hm.ok hpos
    · exact ValW.ok hpos hw m' h

theorem levW_ge : ∀ (n : ℕ) (w : List Move), (∀ m ∈ w, m.Ok) → n ≤ levW n w
  | _, [], _ => le_refl _
  | n, m :: w, hw => (lev_ge (hw m List.mem_cons_self) n).trans
      (levW_ge _ w fun m' hm' => hw m' (List.mem_cons_of_mem _ hm'))

/-- A valid move at level `n` evaluates to its concrete element. -/
theorem lift_hatF (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) {m : Move} {n : ℕ} (hm : m.Val P n) :
    FreeGroup.lift (evGen (P := P)) (hatF P m n) = conc m n := by
  have hok := hm.ok hpos
  cases m with
  | split i p =>
    obtain ⟨hi, hp⟩ := hm
    by_cases h1 : i + 1 < n
    · have e : hatF P (.split i p) n = gF (Sum.inl ⟨p, hp⟩) (i + 1) := by
        simp only [hatF, if_pos h1, dif_pos hp]
      rw [e, lift_gF hpos _ _ (by omega)]
      show conc (.split (i + 1 - 1) p) (i + 1 + 1) = _
      rw [Nat.add_sub_cancel]
      exact (conc_stable_to hok (by omega) (show i + 1 < i + 1 + 1 by omega) n (by omega)).symm
    · have hin : i + 1 = n := by omega
      rcases hp with rfl | hp'
      · have e : hatF P (.split i 2) n = 1 := by
          simp only [hatF, if_neg h1, if_neg (show ¬ (i + 1 = n ∧ (2 : ℕ) ≠ 2) by simp)]
        rw [e, map_one, show i = n - 1 by omega, conc_tail_two (by omega)]
      · have hp2 : p ≠ 2 := fun e => hP2 (e ▸ hp')
        have e : hatF P (.split i p) n = gF (Sum.inr (Sum.inl ⟨p, hp'⟩)) (i + 1) := by
          simp only [hatF, if_neg h1, if_pos (show i + 1 = n ∧ p ≠ 2 from ⟨hin, hp2⟩), dif_pos hp']
        rw [e, lift_gF hpos _ _ (by omega)]
        show conc (.split (i + 1 - 1) p) (i + 1) = _
        rw [Nat.add_sub_cancel, hin]
  | swap k =>
    have hk : k + 1 < n := hm
    by_cases h1 : k + 2 < n
    · have e : hatF P (.swap k) n = gF (Sum.inr (Sum.inr false)) (k + 1) := by
        simp only [hatF, if_pos h1]
      rw [e, lift_gF hpos _ _ (by omega)]
      show conc (.swap (k + 1 - 1)) (k + 1 + 2) = _
      rw [Nat.add_sub_cancel]
      exact (conc_stable_to hok (by omega) (show k + 2 < k + 1 + 2 by omega) n (by omega)).symm
    · have e : hatF P (.swap k) n = gF (Sum.inr (Sum.inr true)) (k + 1) := by
        simp only [hatF, if_neg h1, if_pos (show k + 2 = n by omega)]
      rw [e, lift_gF hpos _ _ (by omega)]
      show conc (.swap (k + 1 - 1)) (k + 1 + 1) = _
      rw [Nat.add_sub_cancel, show k + 1 + 1 = n by omega]

/-- **Evaluation of words.** A valid word at level `n ≥ 1` evaluates to `frac` of the comb onto its
realization. -/
theorem lift_toFree (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P) : ∀ (n : ℕ) (w : List Move),
    0 < n → ValW P n w →
      FreeGroup.lift (evGen (P := P)) (toFree P n w) = frac (comb (levW n w)) (real (comb n) w)
  | n, [], hn, _ => by
    rw [toFree_nil, map_one, levW_nil, real_nil, frac_self (isPart_comb n hn)]
  | n, m :: w, hn, ⟨hm, hw⟩ => by
    have hok := hm.ok hpos
    have hL := lev_pos hn hok
    rw [toFree_cons, map_mul, lift_hatF hpos hP2 hm, lift_toFree hpos hP2 (m.lev n) w hL hw,
      levW_cons, real_cons]
    have pA : IsPart (m.app (comb n)) := isPart_comb_app hn hok
    have pC : IsPart (comb (m.lev n)) := isPart_comb _ hL
    have hlen : (comb (m.lev n)).length = (m.app (comb n)).length := by
      rw [length_app, length_comb, length_comb]
    have wok : ∀ m' ∈ w, m'.Ok := ValW.ok hpos hw
    have e : conc m n = frac (real (comb (m.lev n)) w) (real (m.app (comb n)) w) :=
      eq_frac (isPart_real pC w wok) (isPart_real pA w wok) (forall₂_real (frac_canon pC pA hlen) w)
    have hL' : 0 < levW (m.lev n) w := lt_of_lt_of_le hL (levW_ge _ w wok)
    rw [e, frac_mul (isPart_comb _ hL') (isPart_real pC w wok) (isPart_real pA w wok)
      (by rw [length_comb, length_real, length_comb]) (by rw [length_real, length_real, hlen])]

end GroupApproximation.ClassTransposition.Presentation
