import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.SchreierStep

/-!
# Schreier generators for the orbit of `e_p`: the pivot swap

This is the remaining case of the Schreier step: `s = x_{qj}(1)` with `v_q = v_j = 1`, where
`t = y · wq p q` is the representative for `v`. Then `y = x_{jq}(1) y₀` with `y₀ ∈ Col q (A ∖ j)`,
and the pivot of `s v` moves to `j`. The new representative is `(w y₀ w) · wq p j` with
`w = w_{qj}`, and the Schreier generator lies in `Hp p A`. This is part of Steinberg's proof of
`K₂(𝔽₂) = 0` (Steinberg 1962; Milnor, *Introduction to algebraic K-theory*, §9-10), towards
`simple_kazhdan_sofic_group.tex` l.733-735 (leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVFieldK2

open SteinbergGroup

variable {N : ℕ}

theorem w_congr {a a' b b' : Fin N} (ha : a = a') (hb : b = b') (h : a ≠ b) (h' : a' ≠ b') :
    w a b h = w a' b' h' := by
  subst ha
  subst hb
  rfl

/-- The Weyl part of the swap Schreier generator lies in `Hp p A`. -/
theorem swap_ratio_mem (hN : 3 ≤ N) {p q j : Fin N} {A : Finset (Fin N)} (hp : p ∈ A)
    (hq : q ∈ A) (hj : j ∈ A) (h : q ≠ j) :
    (wq p j)⁻¹ * w q j h * X q j h * wq p q ∈ Hp p A := by
  rw [wq_inv]
  by_cases hqp : q = p
  · subst hqp
    rw [wq_self, mul_one, wq_of_ne (Ne.symm h), w_symm hN q j h, w_mul_self, one_mul]
    exact X_mem_Hp q j h hq hj (Ne.symm h)
  by_cases hjp : j = p
  · subst hjp
    rw [wq_self, one_mul, wq_of_ne h, w_braid hN q j h]
    exact X_mem_Hp j q (Ne.symm h) hj hq h
  have hpj : p ≠ j := Ne.symm hjp
  rw [wq_of_ne hjp, wq_of_ne hqp]
  have h1 : w j p hjp * w q j h * w j p hjp = w q p hqp :=
    (w_conj_w hN j p q j hjp h).trans
      (w_congr (Equiv.swap_apply_of_ne_of_ne h hqp) (Equiv.swap_apply_left j p) _ hqp)
  have h2 : w q p hqp * X q j h * w q p hqp = X p j hpj := w_conj_ac q p j hqp h hpj
  have h3 : w q p hqp * w j p hjp * w q p hqp = w j q (Ne.symm h) :=
    (w_conj_w hN q p j p hqp hjp).trans
      (w_congr (Equiv.swap_apply_of_ne_of_ne (Ne.symm h) hjp) (Equiv.swap_apply_right q p) _
        (Ne.symm h))
  have key : w j p hjp * w q j h * X q j h * w q p hqp = w j q (Ne.symm h) * X p j hpj := by
    calc w j p hjp * w q j h * X q j h * w q p hqp
        = (w j p hjp * w q j h * w j p hjp) * (w j p hjp)⁻¹ * X q j h * w q p hqp := by
          group
      _ = w q p hqp * w j p hjp * X q j h * w q p hqp := by rw [h1, w_inv j p hjp]
      _ = (w q p hqp * w j p hjp * w q p hqp) * ((w q p hqp)⁻¹ * X q j h * w q p hqp) := by
          group
      _ = w j q (Ne.symm h) * X p j hpj := by rw [h3, w_inv q p hqp, h2]
  rw [key]
  have hw : w j q (Ne.symm h) ∈ Hp p A := by
    rw [w]
    exact (Hp p A).mul_mem ((Hp p A).mul_mem (X_mem_Hp j q _ hj hq hqp)
      (X_mem_Hp q j h hq hj hjp)) (X_mem_Hp j q _ hj hq hqp)
  exact (Hp p A).mul_mem hw (X_mem_Hp p j hpj hp hj hjp)

/-- Case `i = q`, `v_j = 1`: the pivot moves from `q` to `j`. -/
theorem step_case3b (hN : 3 ≤ N) {p q : Fin N} {A : Finset (Fin N)} (hp : p ∈ A) (hq : q ∈ A)
    {j : Fin N} (h : q ≠ j) (hj : j ∈ A) {v : Fin N → ZMod 2} (hvj : v j = 1)
    {y : St N} (hy : y ∈ Col q A) (hyv : act y (e q) = v) :
    ∃ t' ∈ Trans p A (act (X q j h) v), t'⁻¹ * (X q j h * (y * wq p q)) ∈ Hp p A := by
  have hjq : j ≠ q := Ne.symm h
  obtain ⟨y₀, hy₀, hyy⟩ := Col_split_erase hj hjq y hy
  have hu : act y₀ (e q) j = 0 := by
    rw [Col_act_apply_of_notMem (Finset.notMem_erase j A) y₀ hy₀, e_ne hjq]
  rcases hyy with hyy | hyy
  · exfalso
    rw [← hyv, hyy, hu] at hvj
    exact absurd hvj (by decide)
  have hgen : ∀ (a b : Fin N) (hab : a ≠ b), (a ∈ A.erase j ∧ q = b) →
      w q j h * X a b hab * (w q j h)⁻¹ ∈ Col j A := by
    rintro a b hab ⟨ha, hqb⟩
    subst hqb
    rw [w_inv, w_conj_ca q j a h hab (Finset.ne_of_mem_erase ha)]
    exact X_mem_Col a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)
  have hy' : w q j h * y₀ * w q j h ∈ Col j A := by
    have key := rootSub_conj (Φ := fun a b => a ∈ A.erase j ∧ q = b) (K := Col j A)
      (w q j h) hgen y₀ hy₀
    rwa [w_inv] at key
  have hXX : X q j h * X j q hjq = w q j h * X q j h := by
    rw [w, mul_assoc (X q j h * X j q h.symm) (X q j h) (X q j h), X_mul_self, mul_one]
  have hsv : act (X q j h) v = act (w q j h * y₀ * w q j h) (e j) := by
    rw [← hyv, hyy, ← act_mul, ← mul_assoc, hXX]
    simp only [act_mul]
    rw [act_w_e q j h, act_X_eq_self q j h hu]
  have hsvj : act (X q j h) v j = 1 := by
    rw [act_X_apply_of_ne q j h v hjq]
    exact hvj
  obtain ⟨c, hc, hce⟩ := Col_conj_X h (Finset.notMem_erase j A) y₀ hy₀
  have hgen2 : ∀ (a b : Fin N) (hab : a ≠ b), (a ∈ A.erase j ∧ a ≠ q ∧ j = b) →
      w q j h * X a b hab * (w q j h)⁻¹ ∈ rootSub (fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ j) := by
    rintro a b hab ⟨ha, haq, hjb⟩
    subst hjb
    rw [w_inv, w_conj_cb q j a h hab haq]
    exact X_mem_rootSub (Φ := fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ j) a q haq
      ⟨Finset.mem_of_mem_erase ha, hq, h⟩
  have hWc : w q j h * c * w q j h ∈ rootSub (fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ j) := by
    have key := rootSub_conj (Φ := fun a b => a ∈ A.erase j ∧ a ≠ q ∧ j = b)
      (K := rootSub (fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ j)) (w q j h) hgen2 c hc
    rwa [w_inv] at key
  refine ⟨w q j h * y₀ * w q j h * wq p j, ⟨j, hj, hsvj, _, hy', hsv.symm, rfl⟩, ?_⟩
  have he : (w q j h * y₀ * w q j h * wq p j)⁻¹ * (X q j h * (y * wq p q)) =
      ((wq p j)⁻¹ * (w q j h * c * w q j h) * wq p j) *
        ((wq p j)⁻¹ * w q j h * X q j h * wq p q) := by
    rw [hyy]
    calc (w q j h * y₀ * w q j h * wq p j)⁻¹ * (X q j h * (X j q hjq * y₀ * wq p q))
        = (wq p j)⁻¹ * (w q j h)⁻¹ * y₀⁻¹ * (w q j h)⁻¹ * (X q j h * X j q hjq) * y₀ *
            wq p q := by group
      _ = (wq p j)⁻¹ * (w q j h)⁻¹ * (y₀⁻¹ * X q j h * y₀) * wq p q := by
          rw [hXX]
          group
      _ = (wq p j)⁻¹ * w q j h * c * (w q j h * w q j h) * X q j h * wq p q := by
          rw [hce, w_mul_self, w_inv]
          group
      _ = _ := by group
  rw [he]
  exact (Hp p A).mul_mem (conj_H hN hp hj _ hWc) (swap_ratio_mem hN hp hq hj h)

end GroupApproximation.Full.LVFieldK2
