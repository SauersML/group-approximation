import GroupApproximation.Kazhdan.KazhdanFixedSpace
import Mathlib.Data.Int.GCD
import GroupApproximation.Meta.AxiomGuard

/-!
# Translate sums and twisted fixed vectors

Two representation-theoretic devices for computing representation angles of finite `p`-groups
without characters, used for the Heisenberg group `U₃(p)` and the Sylow subgroup `U₄(p)` of
`Sp₄(F_p)` (Caprace--Conder--Kaluba--Witzel, arXiv:2011.09276, Proposition 7.3).

* **Translate sums.**  For `b` with `bᵖ = 1` put `T = ∑_{j < p} ρ(bʲ) x`.  Then `T` is `b`-fixed,
  `⟪T, y⟫ = p ⟪x, y⟫` for every `b`-fixed `y`, and `‖T‖² = p ∑_{m < p} ⟪x, ρ(bᵐ) x⟫`.  So
  `p² ⟪x, y⟫² ≤ ‖T‖² ‖y‖²`, and a bound on the Gram sum `∑_m ⟪x, ρ(bᵐ) x⟫` is a bound on the angle
  between `x` and the `b`-fixed space.
* **Twisted fixed vectors.**  If `x` is `a`-fixed, `ρ(a) y = ρ(zⁿ) y` with `z` commuting with `a`,
  `zᵖ = 1` and `zⁿ` generating `⟨z⟩`, and `x ⟂ V^{⟨z⟩}`, then `⟪x, y⟫ = 0`: the correlation is
  invariant under `y ↦ ρ(zⁿ) y`, hence equals its average over `⟨z⟩`, which is `z`-fixed.
-/

namespace GroupApproximation

universe u v

namespace EJZAngleTranslates

open KazhdanFixedSpace

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sum of the first `p` translates of `x` by powers of `b`. -/
noncomputable def translateSum (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (b : G) (p : ℕ) (x : E) : E :=
  ∑ j ∈ Finset.range p, ρ (b ^ j) x

/-- A vector fixed by `b` is fixed by every power of `b`. -/
theorem pow_apply_of_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {b : G} {v : E} (hv : ρ b v = v) (j : ℕ) :
    ρ (b ^ j) v = v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, map_mul]
    change ρ (b ^ j) (ρ b v) = v
    rw [hv, ih]

/-- The fixed space of `⟨b⟩` is the space of `b`-fixed vectors. -/
theorem mem_fixedSubspace_zpowers_iff (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (b : G) (v : E) :
    v ∈ fixedSubspace ρ (Subgroup.zpowers b) ↔ ρ b v = v := by
  constructor
  · intro hv
    exact (mem_fixedSubspace_iff ρ _ v).mp hv b (Subgroup.mem_zpowers b)
  · intro hv
    rw [mem_fixedSubspace_iff]
    intro g hg
    exact fixed_of_mem_closure ρ {b} v
      (fun s hs ↦ by rw [Set.mem_singleton_iff.mp hs]; exact hv) g
      (by rwa [← Subgroup.zpowers_eq_closure])

/-- The translate sum is `b`-fixed when `bᵖ = 1`. -/
theorem translateSum_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {b : G} {p : ℕ} (hb : b ^ p = 1) (x : E) :
    ρ b (translateSum ρ b p x) = translateSum ρ b p x := by
  unfold translateSum
  rw [map_sum]
  have hshift : ∀ j : ℕ, ρ b (ρ (b ^ j) x) = ρ (b ^ (j + 1)) x := by
    intro j
    rw [pow_succ', map_mul]
    rfl
  simp_rw [hshift]
  have h1 : ∑ i ∈ Finset.range (p + 1), ρ (b ^ i) x =
      ∑ i ∈ Finset.range p, ρ (b ^ (i + 1)) x + ρ (b ^ 0) x :=
    Finset.sum_range_succ' _ _
  have h2 : ∑ i ∈ Finset.range (p + 1), ρ (b ^ i) x =
      ∑ i ∈ Finset.range p, ρ (b ^ i) x + ρ (b ^ p) x :=
    Finset.sum_range_succ _ _
  rw [pow_zero] at h1
  rw [hb] at h2
  exact add_right_cancel (h1.symm.trans h2)

/-- Against a `b`-fixed vector the translate sum pairs as `p` copies of `x`. -/
theorem inner_translateSum_of_fixed (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (b : G) (p : ℕ) (x : E) {y : E}
    (hy : ρ b y = y) : inner ℝ (translateSum ρ b p x) y = p * inner ℝ x y := by
  unfold translateSum
  rw [sum_inner]
  have hterm : ∀ j : ℕ, inner ℝ (ρ (b ^ j) x) y = inner ℝ x y := by
    intro j
    calc
      inner ℝ (ρ (b ^ j) x) y = inner ℝ (ρ (b ^ j) x) (ρ (b ^ j) y) := by
        rw [pow_apply_of_fixed ρ hy j]
      _ = inner ℝ x y := LinearIsometryEquiv.inner_map_map _ _ _
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `‖∑_{j<p} ρ(bʲ) x‖² = p ∑_{m<p} ⟪x, ρ(bᵐ) x⟫` when `bᵖ = 1`. -/
theorem norm_sq_translateSum (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {b : G} {p : ℕ} (hb : b ^ p = 1) (x : E) :
    ‖translateSum ρ b p x‖ ^ 2 = p * ∑ m ∈ Finset.range p, inner ℝ x (ρ (b ^ m) x) := by
  rw [← real_inner_self_eq_norm_sq,
    inner_translateSum_of_fixed ρ b p x (translateSum_fixed ρ hb x)]
  unfold translateSum
  rw [inner_sum]

/-- Cauchy--Schwarz against the translate sum: `p² ⟪x, y⟫² ≤ ‖T‖² ‖y‖²` for `b`-fixed `y`. -/
theorem sq_inner_le_of_translateSum (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (b : G) (p : ℕ) (x : E) {y : E}
    (hy : ρ b y = y) :
    (p : ℝ) ^ 2 * inner ℝ x y ^ 2 ≤ ‖translateSum ρ b p x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := inner_translateSum_of_fixed ρ b p x hy
  have hcs := abs_real_inner_le_norm (translateSum ρ b p x) y
  rw [h] at hcs
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [sq_abs] at hsq
  nlinarith [hsq]

/-- If `zᵖ = 1` and `n` is prime to `p`, the powers of `zⁿ` exhaust the powers of `z`. -/
theorem exists_pow_mul_eq_pow {z : G} {p n : ℕ} (hz : z ^ p = 1) (hp : p ≠ 0)
    (hcop : Nat.Coprime n p) (j : ℕ) : ∃ k : ℕ, z ^ (n * k) = z ^ j := by
  obtain ⟨k, _, hk⟩ := Nat.exists_mul_mod_eq_of_coprime j hcop hp
  refine ⟨k, ?_⟩
  rw [pow_eq_pow_mod (n * k) hz, hk, ← pow_eq_pow_mod j hz]

/-- **Twisted fixed vectors are orthogonal off the fixed space of `z`.**  Let `x` be `a`-fixed and
orthogonal to the `⟨z⟩`-fixed vectors, and let `ρ(a) y = ρ(zⁿ) y`, where `z` commutes with `a`,
`zᵖ = 1` and the powers of `zⁿ` exhaust those of `z`.  Then `⟪x, y⟫ = 0`. -/
theorem inner_eq_zero_of_twisted [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {a z : G}
    {p n : ℕ} (hp : 0 < p) (hz : z ^ p = 1) (haz : Commute a z)
    (hgen : ∀ j : ℕ, ∃ k : ℕ, z ^ (n * k) = z ^ j)
    {x y : E} (hx : ρ a x = x) (hy : ρ a y = ρ (z ^ n) y)
    (hxz : x ∈ (fixedSubspace ρ (Subgroup.zpowers z))ᗮ) : inner ℝ x y = 0 := by
  have step1 : ∀ k : ℕ, inner ℝ x (ρ (z ^ (n * k)) y) = inner ℝ x y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcomm : ρ (z ^ (n * k)) (ρ a y) = ρ a (ρ (z ^ (n * k)) y) := by
        have h := congrArg (fun g ↦ ρ g y) (haz.pow_right (n * k)).eq
        simp only [map_mul] at h
        exact h.symm
      calc
        inner ℝ x (ρ (z ^ (n * (k + 1))) y) = inner ℝ x (ρ (z ^ (n * k)) (ρ (z ^ n) y)) := by
          rw [mul_add, mul_one, pow_add, map_mul]
          rfl
        _ = inner ℝ x (ρ (z ^ (n * k)) (ρ a y)) := by rw [hy]
        _ = inner ℝ x (ρ a (ρ (z ^ (n * k)) y)) := by rw [hcomm]
        _ = inner ℝ (ρ a x) (ρ a (ρ (z ^ (n * k)) y)) := by rw [hx]
        _ = inner ℝ x (ρ (z ^ (n * k)) y) := LinearIsometryEquiv.inner_map_map _ _ _
        _ = inner ℝ x y := ih
  have step2 : ∀ j : ℕ, inner ℝ x (ρ (z ^ j) y) = inner ℝ x y := by
    intro j
    obtain ⟨k, hk⟩ := hgen j
    rw [← hk]
    exact step1 k
  have hs : translateSum ρ z p y ∈ fixedSubspace ρ (Subgroup.zpowers z) :=
    (mem_fixedSubspace_zpowers_iff ρ z _).mpr (translateSum_fixed ρ hz y)
  have hxs : inner ℝ x (translateSum ρ z p y) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hs hxz
  have hsum : inner ℝ x (translateSum ρ z p y) = p * inner ℝ x y := by
    unfold translateSum
    rw [inner_sum]
    simp only [step2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  exact (mul_eq_zero.mp (hsum.symm.trans hxs)).resolve_left hp'

end EJZAngleTranslates
end GroupApproximation

#audit_axioms GroupApproximation.EJZAngleTranslates.pow_apply_of_fixed
#audit_axioms GroupApproximation.EJZAngleTranslates.mem_fixedSubspace_zpowers_iff
#audit_axioms GroupApproximation.EJZAngleTranslates.translateSum_fixed
#audit_axioms GroupApproximation.EJZAngleTranslates.inner_translateSum_of_fixed
#audit_axioms GroupApproximation.EJZAngleTranslates.norm_sq_translateSum
#audit_axioms GroupApproximation.EJZAngleTranslates.sq_inner_le_of_translateSum
#audit_axioms GroupApproximation.EJZAngleTranslates.exists_pow_mul_eq_pow
#audit_axioms GroupApproximation.EJZAngleTranslates.inner_eq_zero_of_twisted
