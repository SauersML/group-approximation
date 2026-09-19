import GroupApproximation.ClassTransposition.Out.Kernel

/-!
# Kourovka 17.57, step 3 (core): a periodic regular sequence has a short recurrence

Let `F` be a field and let `f : ℕ → F` satisfy the base-2 recursions of `Out/Kernel.lean`, with
`P`-periodic coefficients and `β₀(k) ≠ 0`. Write `P = 2ᶜ P'` with `P'` odd. If `f` is periodic,
then `f` satisfies a nonzero linear recurrence of order `≤ 2ᶜ · 2P`. The bound does not depend
on `f`'s period (`exists_short_recurrence`).

1. **Halving.** If `T` is a period and `P ∣ T`, then `f(2(k + T) + 0) = f(2k + 0)` gives
   `β₀(k) (f(k + T) - f(k)) = 0`. So a period `2T` halves to `T`, and `f` has a period `P u`
   with `u` odd.
2. **Phases.** Let `2^L ≡ 1 (mod P' u)` (Euler). Then the phase `n ↦ f(2ᶜ(n + s) + r₀)` equals
   the 2-kernel sequence `n ↦ f(2^{c+L} n + 2ᶜ s + r₀)`, so it lies in `W_P(f)`.
3. **Counting.** Consider `g ↦ (r₀ ↦ Σⱼ gⱼ · (phase r₀ of the j-th shift))`. It maps
   `F^{D+1}` into `(W_P(f))^{2ᶜ}`, which has dimension `≤ 2ᶜ · 2P = D`, so it has a nonzero
   kernel vector. That vector is the recurrence.

This replaces the Mahler-function route (`lem: AB`) for 17.57. The period of `Φ mod p` is given by
continuity, and the order bound is uniform in `p`, so `Out/LocalGlobal.lean` applies.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

variable {F : Type*} [Field F]

section
variable {P : ℕ} {f : ℕ → F} {β α : ℕ → ℕ → F}
  (hβ : ∀ e k, β e (k + P) = β e k) (hα : ∀ e k, α e (k + P) = α e k)
  (hβ0 : ∀ k, β 0 k ≠ 0) (hrec : ∀ e k, e < 2 → f (2 * k + e) = β e k * f k + α e k)
include hβ hα hβ0 hrec

theorem half_period {T : ℕ} (hPT : P ∣ T) (hT : ∀ n, f (n + 2 * T) = f n) :
    ∀ n, f (n + T) = f n := by
  intro k
  obtain ⟨q, hq⟩ := hPT
  have h1 := hrec 0 (k + T) (by norm_num)
  have h2 := hrec 0 k (by norm_num)
  have h3 : f (2 * (k + T) + 0) = f (2 * k + 0) := by
    rw [show 2 * (k + T) + 0 = 2 * k + 0 + 2 * T by ring]
    exact hT _
  have hb : β 0 (k + T) = β 0 k := by rw [hq]; exact periodic_add_mul (hβ 0) q k
  have ha : α 0 (k + T) = α 0 k := by rw [hq]; exact periodic_add_mul (hα 0) q k
  rw [h1, h2, hb, ha] at h3
  exact mul_left_cancel₀ (hβ0 k) (by linear_combination h3)

theorem exists_period_mul_odd {T : ℕ} (hT0 : T ≠ 0) (hT : ∀ n, f (n + T) = f n) :
    ∃ u : ℕ, Odd u ∧ ∀ n, f (n + P * u) = f n := by
  obtain ⟨s, u, hu, hTs⟩ := Nat.exists_eq_two_pow_mul_odd hT0
  refine ⟨u, hu, ?_⟩
  have hPT : ∀ n, f (n + P * (2 ^ s * u)) = f n := by
    intro n
    rw [← hTs]
    have := periodic_add_mul hT P n
    rwa [mul_comm] at this
  clear hTs
  induction s with
  | zero => simpa using hPT
  | succ s ih =>
    apply ih
    apply half_period hβ hα hβ0 hrec ⟨2 ^ s * u, rfl⟩
    intro n
    rw [show 2 * (P * (2 ^ s * u)) = P * (2 ^ (s + 1) * u) by ring]
    exact hPT n

end

/-- **Step 3 (core).** A periodic sequence satisfying the base-2 recursions has a nonzero
recurrence of order `≤ 2ᶜ · 2P`, where `P = 2ᶜ P'` with `P'` odd. -/
theorem exists_short_recurrence {P c P' : ℕ} (hP : 0 < P) (hPc : P = 2 ^ c * P') (hP' : Odd P')
    {f : ℕ → F} {β α : ℕ → ℕ → F}
    (hβ : ∀ e k, β e (k + P) = β e k) (hα : ∀ e k, α e (k + P) = α e k)
    (hβ0 : ∀ k, β 0 k ≠ 0) (hrec : ∀ e k, e < 2 → f (2 * k + e) = β e k * f k + α e k)
    {T : ℕ} (hT0 : T ≠ 0) (hT : ∀ n, f (n + T) = f n) :
    ∃ g : Fin (2 ^ c * (2 * P) + 1) → F, g ≠ 0 ∧ ∀ m, ∑ j, g j * f (m + j) = 0 := by
  classical
  obtain ⟨u, hu, hper⟩ := exists_period_mul_odd hβ hα hβ0 hrec hT0 hT
  have hker := kernel_mem_perSpace hP hβ hα hrec
  -- phases lie in `W`
  have hphase : ∀ r₀ s, r₀ < 2 ^ c → (fun n => f (2 ^ c * (n + s) + r₀)) ∈ perSpace P hP f := by
    intro r₀ s hr₀
    have hodd : Odd (P' * u) := hP'.mul hu
    have hcop : Nat.Coprime 2 (P' * u) := Nat.coprime_two_left.mpr hodd
    obtain ⟨L, hL⟩ : ∃ L, L = Nat.totient (P' * u) * (s + 1) := ⟨_, rfl⟩
    have hLmod : 2 ^ L ≡ 1 [MOD P' * u] := by
      have := (Nat.ModEq.pow_totient hcop).pow (s + 1)
      rwa [← pow_mul, one_pow, ← hL] at this
    have htot : 0 < Nat.totient (P' * u) := Nat.totient_pos.mpr hodd.pos
    have hLs : s + 1 ≤ 2 ^ L := by
      have h1 : s + 1 ≤ L := by
        rw [hL]
        exact Nat.le_mul_of_pos_left _ htot
      exact le_trans h1 (Nat.lt_two_pow_self (n := L)).le
    obtain ⟨q, hq⟩ : P' * u ∣ 2 ^ L - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hLmod.symm
    have h2L : 2 ^ L = P' * u * q + 1 := by
      rw [← hq]
      exact (Nat.sub_add_cancel Nat.one_le_two_pow).symm
    have hr : 2 ^ c * s + r₀ < 2 ^ (c + L) := by
      rw [pow_add]
      have h1 := Nat.mul_le_mul_left (2 ^ c) hLs
      rw [mul_add, mul_one] at h1
      linarith
    have hmem := hker (c + L) (2 ^ c * s + r₀) hr
    convert hmem using 1
    funext n
    have e : 2 ^ (c + L) * n + (2 ^ c * s + r₀) = 2 ^ c * (n + s) + r₀ + P * u * (q * n) := by
      rw [pow_add, h2L, hPc]
      ring
    rw [e, periodic_add_mul hper]
  -- every phase of every shift lies in `W`
  have hψ : ∀ (j : ℕ) (r₀ : Fin (2 ^ c)),
      (fun n => f (2 ^ c * n + (r₀ : ℕ) + j)) ∈ perSpace P hP f := by
    intro j r₀
    have hpos : 0 < 2 ^ c := by positivity
    have := hphase (((r₀ : ℕ) + j) % 2 ^ c) (((r₀ : ℕ) + j) / 2 ^ c) (Nat.mod_lt _ hpos)
    convert this using 1
    funext n
    congr 1
    have := Nat.div_add_mod ((r₀ : ℕ) + j) (2 ^ c)
    rw [mul_add]
    linarith
  -- the counting map `F^{D+1} → W^{2ᶜ}`
  let Θ : (Fin (2 ^ c * (2 * P) + 1) → F) →ₗ[F] (Fin (2 ^ c) → perSpace P hP f) :=
    { toFun := fun g r₀ => ⟨∑ j, g j • (fun n => f (2 ^ c * n + (r₀ : ℕ) + (j : ℕ))),
        (perSpace P hP f).sum_mem fun j _ => (perSpace P hP f).smul_mem _ (hψ (j : ℕ) r₀)⟩
      map_add' := fun g g' => by
        funext r₀
        apply Subtype.ext
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add]
      map_smul' := fun a g => by
        funext r₀
        apply Subtype.ext
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul,
          Finset.smul_sum, mul_smul] }
  have hdim : Module.finrank F (Fin (2 ^ c) → perSpace P hP f) < Module.finrank F
      (Fin (2 ^ c * (2 * P) + 1) → F) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h1 := Nat.mul_le_mul_left (2 ^ c) (finrank_perSpace_le P hP f)
    linarith
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := Θ) hdim)
  refine ⟨g, hg0, fun m => ?_⟩
  have hpos : 0 < 2 ^ c := by positivity
  have h0 := congrArg (fun v : Fin (2 ^ c) → perSpace P hP f =>
    ((v ⟨m % 2 ^ c, Nat.mod_lt _ hpos⟩ : perSpace P hP f) : ℕ → F) (m / 2 ^ c))
    (LinearMap.mem_ker.mp hg)
  simp only [Θ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Submodule.coe_zero, Fin.val_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  rw [Nat.div_add_mod] at h0
  exact h0

end GroupApproximation.ClassTransposition.Out
