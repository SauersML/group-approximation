import GroupApproximation.Sofic.HullSuitabilityGeometry
import GroupApproximation.Meta.AxiomGuard

/-!
# The chain lemma with varying edges (Osin 2016, Lemma 2.1)

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Lemma 2.1, from
Ghys--de la Harpe, Chapter 5, Theorem 16:

> Let `(S, d)` be a `δ`-hyperbolic metric space, `s₀, …, sₙ` a sequence of points
> in `S` such that `d(s_{i−1}, s_{i+1}) ≥ max{d(s_{i−1}, s_i), d(s_{i+1}, s_i)} + 18δ + 1`
> for every `i`.  Then `d(s₀, sₙ) ≥ n`.

In Gromov products (Osin's Remark 2.2) the hypothesis reads
`2 (s_{i−1} | s_{i+1})_{s_i} ≤ min{d(s_{i−1}, s_i), d(s_i, s_{i+1})} − 18δ − 1`.
Osin's `δ` is the Rips constant; with the four-point constant of
`HullGeometry.IsHyperbolicSpace` the same argument needs only `2δ`.

## The argument

Put `K > 2δ` and assume at every inner vertex `2·turn + K` is at most both
adjacent edges.  The invariant is
`2 (y₀ | y_{n+1})_{yₙ} + (K − 2δ) ≤ d(yₙ, y_{n+1})`: the initial point is seen from
the current vertex almost straight behind the next one.  One four-point step
carries it to the next vertex, because the backward product at `y_{n+1}` exceeds
the turn there by more than `δ`.  Every edge then adds at least `K − 2δ` to the
distance from `y₀` (`chain_progress_of_turns`).

The repository's `HullGeometry.chain_backtracking_and_progress` is the special
case of constant edges and a constant turn bound.

## Manuscript status

Infrastructure for Osin's Theorem 1.1 (the limit-set spelling of acylindrical
hyperbolicity used in `sec:torsion-free`); certifies no printed sentence on its
own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry

universe u v

variable {X : Type v} [PseudoMetricSpace X]

/-- A four-point constant is nonnegative as soon as the space has a point. -/
theorem nonneg_delta {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (p : X) : 0 ≤ δ := by
  have h := hδ p p p p
  rw [min_self] at h
  linarith

/-- **Osin's Lemma 2.1, four-point form.**  If at every inner vertex twice the
Gromov product of the two neighbours plus `K` is at most both adjacent edges,
and `K > 2δ`, then every edge adds at least `K − 2δ` to the distance from the
initial point, and the initial point stays almost straight behind the next
vertex. -/
theorem chain_progress_of_turns {δ K : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hK : 2 * δ < K) (y : ℕ → X)
    (hin : ∀ n : ℕ,
      2 * gromovProduct (y n) (y (n + 2)) (y (n + 1)) + K ≤ dist (y n) (y (n + 1)))
    (hout : ∀ n : ℕ,
      2 * gromovProduct (y n) (y (n + 2)) (y (n + 1)) + K ≤
        dist (y (n + 1)) (y (n + 2))) :
    ∀ n : ℕ, (K - 2 * δ) * n ≤ dist (y 0) (y n) ∧
      2 * gromovProduct (y 0) (y (n + 1)) (y n) + (K - 2 * δ) ≤ dist (y n) (y (n + 1)) := by
  have hδ0 : 0 ≤ δ := nonneg_delta hδ (y 0)
  intro n
  induction n with
  | zero =>
      refine ⟨by simp, ?_⟩
      show 2 * gromovProduct (y 0) (y 1) (y 0) + (K - 2 * δ) ≤ dist (y 0) (y 1)
      have hz : gromovProduct (y 0) (y 1) (y 0) = 0 := by
        unfold gromovProduct
        rw [dist_self, dist_comm (y 1) (y 0)]
        ring
      have h0 : 2 * gromovProduct (y 0) (y 2) (y 1) + K ≤ dist (y 0) (y 1) := hin 0
      have hT := gromovProduct_nonneg (y 0) (y 2) (y 1)
      rw [hz]
      linarith
  | succ n ih =>
      obtain ⟨hprog, hback⟩ := ih
      have hin' := hin n
      have hout' := hout n
      have hsw : gromovProduct (y 0) (y n) (y (n + 1)) =
          dist (y n) (y (n + 1)) - gromovProduct (y 0) (y (n + 1)) (y n) := by
        unfold gromovProduct
        rw [dist_comm (y (n + 1)) (y n)]
        ring
      have hfar : gromovProduct (y n) (y (n + 2)) (y (n + 1)) + δ <
          gromovProduct (y 0) (y n) (y (n + 1)) := by
        rw [hsw]
        linarith
      have hnext := gromovProduct_le_add_delta_of_lt hδ hfar
      have hd : dist (y 0) (y (n + 1)) =
          dist (y 0) (y n) + dist (y n) (y (n + 1)) -
            2 * gromovProduct (y 0) (y (n + 1)) (y n) := by
        unfold gromovProduct
        rw [dist_comm (y (n + 1)) (y n)]
        ring
      refine ⟨?_, ?_⟩
      · push_cast
        rw [hd]
        linarith
      · show 2 * gromovProduct (y 0) (y (n + 2)) (y (n + 1)) + (K - 2 * δ) ≤
          dist (y (n + 1)) (y (n + 2))
        linarith

/-- **Osin's Lemma 2.1, literal form**: with the margin `2δ + 1`, the chain
advances at unit speed, `d(s₀, sₙ) ≥ n`. -/
theorem le_dist_chain {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (y : ℕ → X)
    (hin : ∀ n : ℕ,
      2 * gromovProduct (y n) (y (n + 2)) (y (n + 1)) + (2 * δ + 1) ≤
        dist (y n) (y (n + 1)))
    (hout : ∀ n : ℕ,
      2 * gromovProduct (y n) (y (n + 2)) (y (n + 1)) + (2 * δ + 1) ≤
        dist (y (n + 1)) (y (n + 2))) :
    ∀ n : ℕ, (n : ℝ) ≤ dist (y 0) (y n) := by
  intro n
  have h := (chain_progress_of_turns hδ (by linarith) y hin hout n).1
  have hK : 2 * δ + 1 - 2 * δ = 1 := by ring
  rw [hK, one_mul] at h
  exact h

variable {G : Type u} [Group G] [MulAction G X]

/-- **A periodic chain certifies a loxodromic element.**  If a group element
shifts the chain by `p > 0` steps and the chain satisfies the turn conditions of
Lemma 2.1, the element is loxodromic at the initial point. -/
theorem isLoxodromic_of_periodic_chain {δ K : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hK : 2 * δ < K) {g : G} (y : ℕ → X) {p : ℕ} (hp : 0 < p)
    (hper : ∀ n : ℕ, y (n + p) = g • y n)
    (hin : ∀ n : ℕ,
      2 * gromovProduct (y n) (y (n + 2)) (y (n + 1)) + K ≤ dist (y n) (y (n + 1)))
    (hout : ∀ n : ℕ,
      2 * gromovProduct (y n) (y (n + 2)) (y (n + 1)) + K ≤
        dist (y (n + 1)) (y (n + 2))) :
    IsLoxodromic g (y 0) := by
  have hall := chain_progress_of_turns hδ hK y hin hout
  have hpow : ∀ k : ℕ, (g ^ k) • y 0 = y (k * p) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', mul_smul, ih, ← hper]
        congr 1
        ring
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨(K - 2 * δ) * p, mul_pos (by linarith) hpR, 0, le_rfl, ?_⟩
  intro k
  rw [hpow k, sub_zero]
  have h := (hall (k * p)).1
  push_cast at h
  calc (K - 2 * δ) * p * k = (K - 2 * δ) * (k * p) := by ring
    _ ≤ dist (y 0) (y (k * p)) := h

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.nonneg_delta
#audit_axioms GroupApproximation.GGT.OsinClassification.chain_progress_of_turns
#audit_axioms GroupApproximation.GGT.OsinClassification.le_dist_chain
#audit_axioms GroupApproximation.GGT.OsinClassification.isLoxodromic_of_periodic_chain
