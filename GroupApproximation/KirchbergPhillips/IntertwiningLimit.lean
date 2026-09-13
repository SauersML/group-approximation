import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Limits of approximate intertwinings

The metric half of Elliott's approximate intertwining argument. Let `α n : A →⋆ₐ[ℂ] B` and
`β n : B →⋆ₐ[ℂ] A` be unital ⋆-homomorphisms between unital C⋆-algebras. Suppose their values on
dense sequences are Cauchy, and the zig-zag composites `β n ∘ α n` and `α (n + 1) ∘ β n` converge to
the identity on those sequences. Then the pointwise limits are mutually inverse ⋆-homomorphisms, so
`A ≃⋆ₐ[ℂ] B`.

## Main results

* `dist_apply_le`: a unital ⋆-homomorphism of C⋆-algebras is 1-Lipschitz.
* `cauchySeq_of_dist_succ_le`, `tendsto_of_dist_le_half_pow`: geometric Cauchy and convergence criteria.
* `cauchySeq_apply_of_denseRange`, `tendsto_apply_of_denseRange`: for 1-Lipschitz maps, being Cauchy
  (converging to the identity) on a dense sequence propagates to every point.
* `tendsto_apply_of_tendsto`: `T n (x n) → y` when `x n → x` and `T n x → y`, for 1-Lipschitz `T n`.
* `exists_starAlgHom_tendsto`: a pointwise Cauchy sequence of ⋆-homomorphisms converges pointwise to
  a ⋆-homomorphism.
* `nonempty_starAlgEquiv_of_tendsto`: the two-sided intertwining limit is a ⋆-isomorphism.

The isomorphism `C*(E(1,1,2)) ≅ C*(E(1,2)) ⊗min C*(E(1,2))` of STW Problem L
(research/artifacts/fz-stw-l-review-2026-09-13.md) goes through this limit.
-/

open Filter Topology

namespace GroupApproximation

namespace KirchbergPhillips

section Metric

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A sequence whose consecutive distances are eventually at most `2 * 2⁻ⁿ` is Cauchy. -/
theorem cauchySeq_of_dist_succ_le {f : ℕ → X} (k : ℕ)
    (h : ∀ n, k ≤ n → dist (f n) (f (n + 1)) ≤ 2 * (1 / 2 : ℝ) ^ n) : CauchySeq f := by
  refine (cauchySeq_shift k).1 (cauchySeq_of_dist_le_of_summable (fun n => 2 * (1 / 2 : ℝ) ^ n)
    (fun n => ?_) (summable_geometric_two.mul_left 2))
  show dist (f (n + k)) (f (n + 1 + k)) ≤ 2 * (1 / 2 : ℝ) ^ n
  rw [Nat.add_right_comm n 1 k]
  exact (h (n + k) (Nat.le_add_left k n)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n k)) (by norm_num))

/-- A sequence eventually within `2⁻ⁿ` of `x` converges to `x`. -/
theorem tendsto_of_dist_le_half_pow {f : ℕ → X} {x : X} (k : ℕ)
    (h : ∀ n, k ≤ n → dist (f n) x ≤ (1 / 2 : ℝ) ^ n) : Tendsto f atTop (𝓝 x) :=
  tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (g := fun n => (1 / 2 : ℝ) ^ n)
    (Eventually.of_forall fun _ => dist_nonneg) ((eventually_ge_atTop k).mono h)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))

/-- For 1-Lipschitz maps `T n`, if `n ↦ T n (s k)` is Cauchy for every term of a dense sequence `s`,
then `n ↦ T n x` is Cauchy for every `x`. -/
theorem cauchySeq_apply_of_denseRange (T : ℕ → X → Y)
    (hT : ∀ n x y, dist (T n x) (T n y) ≤ dist x y) {s : ℕ → X} (hs : DenseRange s)
    (h : ∀ k, CauchySeq fun n => T n (s k)) (x : X) : CauchySeq fun n => T n x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := hs.exists_dist_lt x (div_pos hε (by norm_num : (0 : ℝ) < 3))
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (h k) (ε / 3) (div_pos hε (by norm_num))
  refine ⟨N, fun m hm n hn => ?_⟩
  calc dist (T m x) (T n x)
      ≤ dist (T m x) (T m (s k)) + dist (T m (s k)) (T n (s k)) + dist (T n (s k)) (T n x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
        add_lt_add (add_lt_add ((hT m x (s k)).trans_lt hk) (hN m hm n hn))
          ((hT n (s k) x).trans_lt (by rwa [dist_comm]))
    _ = ε := by ring

/-- For 1-Lipschitz maps `T n`, if `T n (s k) → s k` for every term of a dense sequence `s`, then
`T n x → x` for every `x`. -/
theorem tendsto_apply_of_denseRange (T : ℕ → X → X)
    (hT : ∀ n x y, dist (T n x) (T n y) ≤ dist x y) {s : ℕ → X} (hs : DenseRange s)
    (h : ∀ k, Tendsto (fun n => T n (s k)) atTop (𝓝 (s k))) (x : X) :
    Tendsto (fun n => T n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := hs.exists_dist_lt x (div_pos hε (by norm_num : (0 : ℝ) < 3))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (h k) (ε / 3) (div_pos hε (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  calc dist (T n x) x ≤ dist (T n x) (T n (s k)) + dist (T n (s k)) (s k) + dist (s k) x :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
        add_lt_add (add_lt_add ((hT n x (s k)).trans_lt hk) (hN n hn)) (by rwa [dist_comm])
    _ = ε := by ring

/-- For 1-Lipschitz maps `T n`, `T n (x n) → y₀` when `x n → x₀` and `T n x₀ → y₀`. -/
theorem tendsto_apply_of_tendsto (T : ℕ → X → Y)
    (hT : ∀ n x y, dist (T n x) (T n y) ≤ dist x y) {x : ℕ → X} {x₀ : X} {y₀ : Y}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto (fun n => T n x₀) atTop (𝓝 y₀)) :
    Tendsto (fun n => T n (x n)) atTop (𝓝 y₀) := by
  rw [tendsto_iff_dist_tendsto_zero] at hx hy ⊢
  refine squeeze_zero (g := fun n => dist (x n) x₀ + dist (T n x₀) y₀) (fun _ => dist_nonneg)
    (fun n => (dist_triangle _ (T n x₀) _).trans (add_le_add (hT n (x n) x₀) le_rfl)) ?_
  simpa only [add_zero] using hx.add hy

end Metric

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A unital ⋆-homomorphism between C⋆-algebras is 1-Lipschitz. -/
theorem dist_apply_le (φ : A →⋆ₐ[ℂ] B) (x y : A) : dist (φ x) (φ y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le φ (x - y)

/-- A pointwise Cauchy sequence of unital ⋆-homomorphisms into a C⋆-algebra converges pointwise to a
unital ⋆-homomorphism. -/
theorem exists_starAlgHom_tendsto (α : ℕ → A →⋆ₐ[ℂ] B) (h : ∀ x, CauchySeq fun n => α n x) :
    ∃ L : A →⋆ₐ[ℂ] B, ∀ x, Tendsto (fun n => α n x) atTop (𝓝 (L x)) := by
  choose f hf using fun x => cauchySeq_tendsto_of_complete (h x)
  refine ⟨{ toFun := f
            map_one' := tendsto_nhds_unique (hf 1) (by simp only [map_one]; exact tendsto_const_nhds)
            map_mul' := fun x y => tendsto_nhds_unique (hf (x * y))
              (by simp only [map_mul]; exact (hf x).mul (hf y))
            map_zero' := tendsto_nhds_unique (hf 0) (by simp only [map_zero]; exact tendsto_const_nhds)
            map_add' := fun x y => tendsto_nhds_unique (hf (x + y))
              (by simp only [map_add]; exact (hf x).add (hf y))
            commutes' := fun r => tendsto_nhds_unique (hf (algebraMap ℂ A r))
              (by simp only [AlgHomClass.commutes]; exact tendsto_const_nhds)
            map_star' := fun x => tendsto_nhds_unique (hf (star x))
              (by simp only [map_star]; exact (hf x).star) }, hf⟩

/-- **Two-sided approximate intertwining limit.** If `α n (s k)` and `β n (t k)` are Cauchy on dense
sequences `s`, `t`, and `β n (α n (s k)) → s k`, `α (n + 1) (β n (t k)) → t k`, then `A ≃⋆ₐ[ℂ] B`. -/
theorem nonempty_starAlgEquiv_of_tendsto (α : ℕ → A →⋆ₐ[ℂ] B) (β : ℕ → B →⋆ₐ[ℂ] A)
    {s : ℕ → A} {t : ℕ → B} (hs : DenseRange s) (ht : DenseRange t)
    (hα : ∀ k, CauchySeq fun n => α n (s k)) (hβ : ∀ k, CauchySeq fun n => β n (t k))
    (hβα : ∀ k, Tendsto (fun n => β n (α n (s k))) atTop (𝓝 (s k)))
    (hαβ : ∀ k, Tendsto (fun n => α (n + 1) (β n (t k))) atTop (𝓝 (t k))) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  obtain ⟨L, hL⟩ := exists_starAlgHom_tendsto α
    (cauchySeq_apply_of_denseRange (fun n x => α n x) (fun n => dist_apply_le (α n)) hs hα)
  obtain ⟨M, hM⟩ := exists_starAlgHom_tendsto β
    (cauchySeq_apply_of_denseRange (fun n y => β n y) (fun n => dist_apply_le (β n)) ht hβ)
  have hML : ∀ x, M (L x) = x := fun x => tendsto_nhds_unique
    (tendsto_apply_of_tendsto (fun n y => β n y) (fun n => dist_apply_le (β n)) (hL x) (hM (L x)))
    (tendsto_apply_of_denseRange (fun n y => β n (α n y))
      (fun n y z => (dist_apply_le (β n) _ _).trans (dist_apply_le (α n) y z)) hs hβα x)
  have hLM : ∀ y, L (M y) = y := fun y => tendsto_nhds_unique
    (tendsto_apply_of_tendsto (fun n z => α (n + 1) z) (fun n => dist_apply_le (α (n + 1))) (hM y)
      ((hL (M y)).comp (tendsto_add_atTop_nat 1)))
    (tendsto_apply_of_denseRange (fun n z => α (n + 1) (β n z))
      (fun n z w => (dist_apply_le (α (n + 1)) _ _).trans (dist_apply_le (β n) z w)) ht hαβ y)
  exact ⟨StarAlgEquiv.ofStarAlgHom L M (StarAlgHom.ext hML) (StarAlgHom.ext hLM)⟩

end KirchbergPhillips

end GroupApproximation
