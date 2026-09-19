import Mathlib

/-!
# Kourovka 17.57, step 2: the 2-kernel lies in a space of dimension `≤ 2P`

Let `F` be a field, and let `f : ℕ → F` satisfy base-2 dilation recursions with `P`-periodic
coefficients:

    f(2k + e) = β_e(k) f(k) + α_e(k)     (e ∈ {0, 1}).

Let `W_P(f)` (`perSpace`) be the space of sequences `n ↦ χ(n) f(n) + χ'(n)` with `χ, χ'` of
period `P`. It has dimension `≤ 2P`, and every 2-kernel sequence `n ↦ f(2ʲ n + r)` with
`r < 2ʲ` lies in it (`kernel_mem_perSpace`). This is the regularity of step 2 of
`ct-z-normalizers-are-2-and-3-regular`, over any field. Step 3 uses it modulo `p`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ClassTransposition.Out

variable {F : Type*} [Field F]

theorem periodic_add_mul {a : ℕ → F} {P : ℕ} (ha : ∀ n, a (n + P) = a n) :
    ∀ q n, a (n + P * q) = a n := by
  intro q
  induction q with
  | zero => intro n; simp
  | succ q ih =>
    intro n
    rw [show n + P * (q + 1) = n + P * q + P by ring, ha, ih]

theorem periodic_mod {a : ℕ → F} {P : ℕ} (ha : ∀ n, a (n + P) = a n) (n : ℕ) :
    a (n % P) = a n := by
  conv_rhs => rw [← Nat.mod_add_div n P]
  rw [periodic_add_mul ha]

/-- `(χ, χ') ↦ (n ↦ χ(n mod P) f(n) + χ'(n mod P))`. -/
def perMap (P : ℕ) (hP : 0 < P) (f : ℕ → F) : (Fin P → F) × (Fin P → F) →ₗ[F] (ℕ → F) where
  toFun ab n := ab.1 ⟨n % P, Nat.mod_lt n hP⟩ * f n + ab.2 ⟨n % P, Nat.mod_lt n hP⟩
  map_add' x y := by
    funext n
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext n
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The space `W_P(f)` of sequences `χ f + χ'` with `χ, χ'` of period `P`. -/
def perSpace (P : ℕ) (hP : 0 < P) (f : ℕ → F) : Submodule F (ℕ → F) :=
  LinearMap.range (perMap P hP f)

instance (P : ℕ) (hP : 0 < P) (f : ℕ → F) : FiniteDimensional F (perSpace P hP f) := by
  unfold perSpace
  infer_instance

theorem finrank_perSpace_le (P : ℕ) (hP : 0 < P) (f : ℕ → F) :
    Module.finrank F (perSpace P hP f) ≤ 2 * P := by
  unfold perSpace
  calc Module.finrank F (LinearMap.range (perMap P hP f))
      ≤ Module.finrank F ((Fin P → F) × (Fin P → F)) := LinearMap.finrank_range_le _
    _ = 2 * P := by
      rw [Module.finrank_prod, Module.finrank_fin_fun]
      ring

theorem mem_perSpace {P : ℕ} (hP : 0 < P) {f g : ℕ → F} (a b : ℕ → F)
    (ha : ∀ n, a (n + P) = a n) (hb : ∀ n, b (n + P) = b n)
    (hg : ∀ n, g n = a n * f n + b n) : g ∈ perSpace P hP f := by
  show g ∈ LinearMap.range (perMap P hP f)
  rw [LinearMap.mem_range]
  refine ⟨(fun i => a i, fun i => b i), ?_⟩
  funext n
  show a (n % P) * f n + b (n % P) = g n
  rw [hg n, periodic_mod ha n, periodic_mod hb n]

/-- **Step 2.** Every 2-kernel sequence `n ↦ f(2ʲ n + r)` (`r < 2ʲ`) has the form `χ f + χ'`
with `χ, χ'` of period `P`. -/
theorem kernel_form {P : ℕ} {f : ℕ → F} {β α : ℕ → ℕ → F}
    (hβ : ∀ e k, β e (k + P) = β e k) (hα : ∀ e k, α e (k + P) = α e k)
    (hrec : ∀ e k, e < 2 → f (2 * k + e) = β e k * f k + α e k) :
    ∀ j r, r < 2 ^ j → ∃ a b : ℕ → F, (∀ n, a (n + P) = a n) ∧ (∀ n, b (n + P) = b n) ∧
      ∀ n, f (2 ^ j * n + r) = a n * f n + b n := by
  intro j
  induction j with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    exact ⟨fun _ => 1, fun _ => 0, fun _ => rfl, fun _ => rfl, fun n => by simp⟩
  | succ j ih =>
    intro r hr
    have hr' : r / 2 < 2 ^ j := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rw [pow_succ] at hr
      exact hr
    obtain ⟨a, b, ha, hb, hab⟩ := ih (r / 2) hr'
    have he : r % 2 < 2 := Nat.mod_lt r (by norm_num)
    have hshift : ∀ (g : ℕ → F), (∀ n, g (n + P) = g n) → ∀ n,
        g (2 ^ j * (n + P) + r / 2) = g (2 ^ j * n + r / 2) := by
      intro g hg n
      rw [show 2 ^ j * (n + P) + r / 2 = 2 ^ j * n + r / 2 + P * 2 ^ j by ring,
        periodic_add_mul hg]
    refine ⟨fun n => β (r % 2) (2 ^ j * n + r / 2) * a n,
      fun n => β (r % 2) (2 ^ j * n + r / 2) * b n + α (r % 2) (2 ^ j * n + r / 2),
      fun n => ?_, fun n => ?_, fun n => ?_⟩
    · try simp only
      rw [hshift _ (hβ (r % 2)) n, ha]
    · try simp only
      rw [hshift _ (hβ (r % 2)) n, hshift _ (hα (r % 2)) n, hb]
    · have e : 2 ^ (j + 1) * n + r = 2 * (2 ^ j * n + r / 2) + r % 2 := by
        have := Nat.div_add_mod r 2
        rw [pow_succ]
        linarith
      rw [e, hrec _ _ he, hab]
      try simp only
      ring

theorem kernel_mem_perSpace {P : ℕ} (hP : 0 < P) {f : ℕ → F} {β α : ℕ → ℕ → F}
    (hβ : ∀ e k, β e (k + P) = β e k) (hα : ∀ e k, α e (k + P) = α e k)
    (hrec : ∀ e k, e < 2 → f (2 * k + e) = β e k * f k + α e k) (j r : ℕ) (hr : r < 2 ^ j) :
    (fun n => f (2 ^ j * n + r)) ∈ perSpace P hP f := by
  obtain ⟨a, b, ha, hb, hab⟩ := kernel_form hβ hα hrec j r hr
  exact mem_perSpace hP a b ha hb hab

end GroupApproximation.ClassTransposition.Out
