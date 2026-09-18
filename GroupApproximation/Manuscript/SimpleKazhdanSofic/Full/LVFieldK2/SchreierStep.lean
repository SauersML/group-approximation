import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFieldK2.Transversal

/-!
# Schreier generators for the orbit of `e_p`: the easy cases

Let `t = y · wq p q` be a representative for `v` and `s = x_{ij}(1)` with `i, j ∈ A`. We find
a representative `t'` for `s v` with `t'⁻¹ s t ∈ Hp p A` in three cases: `i, j ≠ q`, `j = q`, and
`i = q` with `v_j = 0`. The last case, `i = q` with `v_j = 1`, is in `SchreierSwap`. These
Schreier generators come from Steinberg's proof of `K₂(𝔽₂) = 0` (Steinberg 1962; Milnor,
*Introduction to algebraic K-theory*, §9-10), towards `simple_kazhdan_sofic_group.tex`
l.733-735 (leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVFieldK2

open SteinbergGroup

variable {N : ℕ}

/-- Case `i ≠ q`, `j ≠ q`: the representative `(s y s) · wq p q`. -/
theorem step_case1 (hN : 3 ≤ N) {p q : Fin N} {A : Finset (Fin N)} (hp : p ∈ A) (hq : q ∈ A)
    {i j : Fin N} (h : i ≠ j) (hi : i ∈ A) (hj : j ∈ A) (hiq : i ≠ q) (hjq : j ≠ q)
    {v : Fin N → ZMod 2} (hq1 : v q = 1) {y : St N} (hy : y ∈ Col q A)
    (hyv : act y (e q) = v) :
    ∃ t' ∈ Trans p A (act (X i j h) v), t'⁻¹ * (X i j h * (y * wq p q)) ∈ Hp p A := by
  have hgen : ∀ (a b : Fin N) (hab : a ≠ b), (a ∈ A ∧ q = b) →
      X i j h * X a b hab * (X i j h)⁻¹ ∈ Col q A := by
    rintro a b hab ⟨ha, hqb⟩
    subst hqb
    rw [X_inv]
    by_cases hja : j = a
    · subst hja
      rw [X_conj_adj i j q h hab hiq]
      exact (Col q A).mul_mem (X_mem_Col i hi hiq) (X_mem_Col j hj hab)
    · rw [X_comm i j a q h hab hja (Ne.symm hiq), mul_assoc, X_mul_self, mul_one]
      exact X_mem_Col a ha hab
  have hsy : X i j h * y * (X i j h)⁻¹ ∈ Col q A :=
    rootSub_conj (Φ := fun a b => a ∈ A ∧ q = b) (K := Col q A) (X i j h) hgen y hy
  rw [X_inv] at hsy
  have hse : act (X i j h) (e q) = e q := act_X_eq_self i j h (e_ne hjq)
  refine ⟨X i j h * y * X i j h * wq p q,
    ⟨q, hq, ?_, X i j h * y * X i j h, hsy, ?_, rfl⟩, ?_⟩
  · rw [act_X_apply_of_ne i j h v (Ne.symm hiq)]
    exact hq1
  · rw [act_mul, act_mul, hse, hyv]
  · have he : (X i j h * y * X i j h * wq p q)⁻¹ * (X i j h * (y * wq p q)) =
        (wq p q)⁻¹ * (X i j h)⁻¹ * wq p q := by group
    rw [he, X_inv]
    exact conj_H hN hp hq (X i j h) (X_mem_rootSub i j h ⟨hi, hj, hjq⟩)

/-- Case `j = q`: the representative `(s y) · wq p q`, with trivial Schreier generator. -/
theorem step_case2 {p q : Fin N} {A : Finset (Fin N)} (hq : q ∈ A) {i : Fin N} (h : i ≠ q)
    (hi : i ∈ A) {v : Fin N → ZMod 2} (hq1 : v q = 1) {y : St N} (hy : y ∈ Col q A)
    (hyv : act y (e q) = v) :
    ∃ t' ∈ Trans p A (act (X i q h) v), t'⁻¹ * (X i q h * (y * wq p q)) ∈ Hp p A := by
  refine ⟨X i q h * y * wq p q,
    ⟨q, hq, ?_, X i q h * y, (Col q A).mul_mem (X_mem_Col i hi h) hy, ?_, rfl⟩, ?_⟩
  · rw [act_X_apply_of_ne i q h v (Ne.symm h)]
    exact hq1
  · rw [act_mul, hyv]
  · have he : (X i q h * y * wq p q)⁻¹ * (X i q h * (y * wq p q)) = 1 := by group
    rw [he]
    exact Subgroup.one_mem _

/-- Case `i = q`, `v_j = 0`: `s` fixes `v`, and `t` itself is the new representative. -/
theorem step_case3a (hN : 3 ≤ N) {p q : Fin N} {A : Finset (Fin N)} (hp : p ∈ A) (hq : q ∈ A)
    {j : Fin N} (h : q ≠ j) (hj : j ∈ A) {v : Fin N → ZMod 2} (hq1 : v q = 1) (hvj : v j = 0)
    {y : St N} (hy : y ∈ Col q A) (hyv : act y (e q) = v) :
    ∃ t' ∈ Trans p A (act (X q j h) v), t'⁻¹ * (X q j h * (y * wq p q)) ∈ Hp p A := by
  have hsv : act (X q j h) v = v := act_X_eq_self q j h hvj
  obtain ⟨y₀, hy₀, hyy⟩ := Col_split_erase hj (Ne.symm h) y hy
  rcases hyy with hyy | hyy
  · obtain ⟨c, hc, hce⟩ := Col_conj_X h (Finset.notMem_erase j A) y₀ hy₀
    have hle : rootSub (fun a b => a ∈ A.erase j ∧ a ≠ q ∧ j = b) ≤
        rootSub (fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ q) :=
      rootSub_mono (Φ := fun a b => a ∈ A.erase j ∧ a ≠ q ∧ j = b)
        (Ψ := fun a b => a ∈ A ∧ b ∈ A ∧ b ≠ q) fun _ _ _ hΦ =>
          ⟨Finset.mem_of_mem_erase hΦ.1, by rw [← hΦ.2.2]; exact hj,
            by rw [← hΦ.2.2]; exact Ne.symm h⟩
    refine ⟨y * wq p q, ?_, ?_⟩
    · rw [hsv]
      exact ⟨q, hq, hq1, y, hy, hyv, rfl⟩
    · have he : (y * wq p q)⁻¹ * (X q j h * (y * wq p q)) =
          (wq p q)⁻¹ * (y⁻¹ * X q j h * y) * wq p q := by group
      rw [he, hyy, hce]
      exact conj_H hN hp hq (c * X q j h)
        (Subgroup.mul_mem _ (hle hc) (X_mem_rootSub q j h ⟨hq, hj, Ne.symm h⟩))
  · exfalso
    have h1 : act y₀ (e q) j = 0 := by
      rw [Col_act_apply_of_notMem (Finset.notMem_erase j A) y₀ hy₀, e_ne (Ne.symm h)]
    have h2 : act y₀ (e q) q = 1 := by rw [Col_act_apply_self y₀ hy₀, e_self]
    rw [← hyv, hyy, act_mul, act_X_apply_self, h1, h2] at hvj
    exact absurd hvj (by decide)

end GroupApproximation.Full.LVFieldK2
