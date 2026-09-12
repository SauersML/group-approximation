import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Moving a short interval into `(0, 1)`

Hyde–Lodha use, in Lemmas 4.3, 4.5 and 4.6, the second half of their Proposition 3.4: "for each
closed interval `I ⊂ ℝ`, `|I| < 1`, and any nonempty open interval `U ⊂ ℝ`, there is an `f ∈ Q_n`
such that `I·f ⊂ U`", which they derive from minimality through a general result on groups acting
on the line (Deroin–Navas–Rivas, Theorem 3.5.19).  What the three lemmas need is weaker, and here it
is proved directly from explicit elements, with no appeal to that result:

**D3 (`exists_move_into_unit`).**  For `a < b` in `ℤ[1/6]` with `b - a < 1` there are `g ∈ Γ₂` and
`j ∈ ℤ` with `0 < g a + j` and `g b + j < 1`.

Write `a = a' + n`, `b = c + (n + 1)` with `a' = fract a` and `c < a'`.
* `a' > 0`, `c < 0`: `[a, b] ⊂ (n, n + 1)` already; `g = 1`.
* `a' = 0`: a periodic `F_6` element moves `c + 1 ∈ (0, 1)` into `(0, 1/3)`, where Hyde–Lodha's `λ`
  (`lamPerm`) has the piece `t ↦ t/6 + 5/18`, and `λ 0 = 5/18`.
* `a' > 0`, `c ≥ 0`: a periodic `F_6` element moves `a'` into `(31/36, 1)` and `c` into `[0, 1/3)`
  (keeping `c = 0` fixed); `λ` maps `(31/36, 1)` above `1` by `t ↦ 2t - 13/18`, and `1 + c` to
  `1 + c/6 + 5/18 < 2`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

theorem lamPerm_add_int (t : ℚ) (k : ℤ) : lamPerm (t + k) = lamPerm t + k := by
  rw [lamPerm_apply, lamPerm_apply]
  exact lamFun_add_int t k

theorem lamPerm_piece1 {s : ℚ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 3) : lamPerm s = s / 6 + 5 / 18 := by
  rw [lamPerm_apply, lamFun_of_mem h0 (by linarith), lamOne_piece1 h1]

theorem lamPerm_piece4 {s : ℚ} (h0 : 31 / 36 ≤ s) (h1 : s ≤ 1) : lamPerm s = 2 * s - 13 / 18 := by
  rw [lamPerm_apply, lamFun_of_mem (by linarith) h1, lamOne_piece4 h0]

theorem one_mem_grid_six (M : ℕ) : (1 : ℚ) ∈ Grid 6 M := by
  simpa using int_mem_grid (m := 6) M 1

/-- **D3.** -/
theorem exists_move_into_unit {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M) (hb : ∃ M, b ∈ Grid 6 M)
    (hab : a < b) (hba : b - a < 1) :
    ∃ g ∈ gammaTwo, ∃ j : ℤ, 0 < g a + j ∧ g b + j < 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ⌊a⌋ = n := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℚ, Int.fract a = a' := ⟨_, rfl⟩
  have hfr0 : 0 ≤ a' := by rw [← ha']; exact Int.fract_nonneg a
  have hfr1 : a' < 1 := by rw [← ha']; exact Int.fract_lt_one a
  have hag : ∃ M, a' ∈ Grid 6 M := by rw [← ha']; exact fract_grid ha
  have hadec : a = a' + n := by rw [← ha', ← hn, Int.fract_add_floor]
  obtain ⟨c, hbdec⟩ : ∃ c : ℚ, b = c + ((n + 1 : ℤ) : ℚ) := ⟨b - ((n + 1 : ℤ) : ℚ), by ring⟩
  have hcg : ∃ M, c ∈ Grid 6 M := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    have h := grid_sub hM (int_mem_grid M (n + 1))
    rwa [hbdec, add_sub_cancel_right] at h
  subst hadec hbdec
  have hca : c < a' := by push_cast at hba; linarith
  have hca1 : a' - 1 < c := by push_cast at hab; linarith
  have hmemP : ∀ x : ↥(compactF 4 1), lamPerm * perHom 4 x ∈ gammaTwo := fun x =>
    gammaTwo.mul_mem lamPerm_mem_gammaTwo (perHom_mem_gammaTwo x)
  rcases lt_or_eq_of_le hfr0 with ha0 | ha0
  · rcases lt_trichotomy c 0 with hc | hc | hc
    · -- `[a, b] ⊂ (n, n + 1)`
      refine ⟨1, gammaTwo.one_mem, -n, ?_, ?_⟩ <;> simp only [Equiv.Perm.one_apply] <;> push_cast <;>
        linarith
    · -- `b = n + 1`
      subst hc
      obtain ⟨x, hx0, hx1, hxres, hxg⟩ := exists_resEq_mem_Ioo (m := 4) hag
        (show (31 / 36 : ℚ) < 1 by norm_num)
      obtain ⟨p, -, hpx⟩ := exists_perCore_apply hag hxg hxres ha0 hfr1 (by linarith) hx1
      refine ⟨lamPerm * perHom 4 p, hmemP p, -(n + 1), ?_, ?_⟩
      · simp only [Equiv.Perm.mul_apply]
        rw [perHom_add_int, hpx, lamPerm_add_int, lamPerm_piece4 hx0.le hx1.le]
        push_cast
        linarith
      · simp only [Equiv.Perm.mul_apply]
        have hP : perHom 4 p (0 + ((n + 1 : ℤ) : ℚ)) = 0 + ((n + 1 : ℤ) : ℚ) := by
          rw [zero_add]
          exact perHom_apply_intCast p (n + 1)
        rw [hP, lamPerm_add_int, lamPerm_zero]
        push_cast
        linarith
    · -- `b > n + 1`: move `c` and `a'` together
      obtain ⟨y, hy0, hy1, hyres, hyg⟩ := exists_resEq_mem_Ioo (m := 4) hcg
        (show (0 : ℚ) < 1 / 3 by norm_num)
      obtain ⟨x, hx0, hx1, hxres, hxg⟩ := exists_resEq_mem_Ioo (m := 4) hag
        (show (31 / 36 : ℚ) < 1 by norm_num)
      obtain ⟨k, hk, hkc, hka⟩ := exists_compactCore_mapsTo (m := 4) hcg hag hyg hxg hyres hxres
        hc hca hfr1 hy0 (by linarith) hx1
      obtain ⟨p, hpdef⟩ : ∃ p : ↥(compactF 4 1), (p : Equiv.Perm ℚ) = k :=
        ⟨⟨k, compactCore_le hk⟩, rfl⟩
      have hpc : perHom 4 p c = y := by
        rw [perHom_apply_of_mem 4 p hc.le (by linarith), hpdef]
        exact hkc
      have hpa : perHom 4 p a' = x := by
        rw [perHom_apply_of_mem 4 p hfr0 hfr1, hpdef]
        exact hka
      refine ⟨lamPerm * perHom 4 p, hmemP p, -(n + 1), ?_, ?_⟩
      · simp only [Equiv.Perm.mul_apply]
        rw [perHom_add_int, hpa, lamPerm_add_int, lamPerm_piece4 hx0.le hx1.le]
        push_cast
        linarith
      · simp only [Equiv.Perm.mul_apply]
        rw [perHom_add_int, hpc, lamPerm_add_int, lamPerm_piece1 hy0.le hy1.le]
        push_cast
        linarith
  · -- `a = n`
    subst ha0
    have hc1g : ∃ M, c + 1 ∈ Grid 6 M := by
      obtain ⟨M, hM⟩ := hcg
      exact ⟨M, grid_add hM (one_mem_grid_six M)⟩
    obtain ⟨y, hy0, hy1, hyres, hyg⟩ := exists_resEq_mem_Ioo (m := 4) hc1g
      (show (0 : ℚ) < 1 / 3 by norm_num)
    obtain ⟨p, -, hpy⟩ := exists_perCore_apply hc1g hyg hyres (by linarith) (by linarith) hy0
      (by linarith)
    refine ⟨lamPerm * perHom 4 p, hmemP p, -n, ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      have hP : perHom 4 p (0 + (n : ℚ)) = 0 + (n : ℚ) := by
        rw [zero_add]
        exact perHom_apply_intCast p n
      rw [hP, lamPerm_add_int, lamPerm_zero]
      push_cast
      linarith
    · simp only [Equiv.Perm.mul_apply]
      have e : c + ((n + 1 : ℤ) : ℚ) = (c + 1) + (n : ℚ) := by push_cast; ring
      rw [e, perHom_add_int, hpy, lamPerm_add_int, lamPerm_piece1 hy0.le hy1.le]
      push_cast
      linarith

#audit_axioms GroupApproximation.HydeLodha.exists_move_into_unit

end HydeLodha
end GroupApproximation
