import GroupApproximation.Kazhdan.GroupRingLaplacian
import GroupApproximation.Kazhdan.PositiveOperatorGap

/-!
# From Laplacian certificates to property (T)

This file is the analytic interface between a finite sum-of-squares
calculation and Kazhdan's property (T).  A later, purely algebraic layer can
establish `IsUniformLaplacianGap` by evaluating an exact group-ring identity.
The theorems here turn that uniform positive gap into a Kazhdan pair and hence
property (T).
-/

namespace GroupApproximation
namespace LaplacianSOSCertificate

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]

/-- A representation-level Laplacian certificate.  It says that the
quadratic form of the finite-set Laplacian is uniformly bounded below on the
orthogonal complement of the invariant vectors, in every complete real
Hilbert-space representation.

An exact group-ring sum-of-squares identity is intended to prove this
predicate without introducing any additional analytic assumptions. -/
def IsUniformLaplacianGap (S : Finset G) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E],
      ∀ (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E),
        x ∈ (KazhdanOrthogonal.invariantSubmodule ρ)ᗮ →
          κ * ‖x‖ ^ 2 ≤
            PositiveOperatorGap.energy (GroupRingLaplacian.laplacian S ρ) x

/-- A uniform Laplacian gap yields any positive Kazhdan tolerance whose
finite-set energy budget is strictly smaller than twice the gap. -/
theorem isKazhdanPair_of_uniformLaplacianGap
    (S : Finset G) {κ ε : ℝ} (hgap : IsUniformLaplacianGap.{u, v} S κ)
    (hε : 0 < ε) (hbudget : (S.card : ℝ) * ε ^ 2 < 2 * κ) :
    IsKazhdanPair.{u, v} G S ε := by
  refine ⟨hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  by_contra hexists
  have hno : IsKazhdanPair.HasNoInvariantVectors G ρ := by
    intro y hy
    by_contra hy0
    exact hexists ⟨y, hy0, hy⟩
  have hxorth : x ∈ (KazhdanOrthogonal.invariantSubmodule ρ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hyzero : y = 0 :=
      hno y ((KazhdanOrthogonal.mem_invariantSubmodule ρ y).mp hy)
    subst y
    simp
  have hlower := hgap.2 E ρ x hxorth
  change κ * ‖x‖ ^ 2 ≤
    inner ℝ x (GroupRingLaplacian.laplacian S ρ x) at hlower
  rw [hx, one_pow, mul_one] at hlower
  have hterm (g : G) (hg : g ∈ S) :
      ‖ρ g x - x‖ ^ 2 ≤ ε ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hε.le).2 (hnear g hg).le
  have hsum :
      ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 ≤ (S.card : ℝ) * ε ^ 2 := by
    calc
      ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 ≤ ∑ _g ∈ S, ε ^ 2 := by
        exact Finset.sum_le_sum fun g hg ↦ hterm g hg
      _ = (S.card : ℝ) * ε ^ 2 := by simp
  have henergy := GroupRingLaplacian.two_mul_inner_laplacian S ρ x
  have : 2 * κ ≤ (S.card : ℝ) * ε ^ 2 := by
    calc
      2 * κ ≤ 2 * inner ℝ x (GroupRingLaplacian.laplacian S ρ x) := by
        linarith
      _ = ∑ g ∈ S, ‖ρ g x - x‖ ^ 2 := henergy
      _ ≤ (S.card : ℝ) * ε ^ 2 := hsum
  exact (not_le_of_gt hbudget) this

/-- Every positive uniform Laplacian gap supplies an explicit Kazhdan pair.
The chosen tolerance is `sqrt (κ / (|S| + 1))`; the extra `1` avoids a
separate nonemptiness assumption on `S`. -/
theorem hasKazhdanPropertyT_of_uniformLaplacianGap
    (S : Finset G) {κ : ℝ} (hgap : IsUniformLaplacianGap.{u, v} S κ) :
    HasKazhdanPropertyT.{u, v} G := by
  let n : ℝ := S.card
  let ε : ℝ := Real.sqrt (κ / (n + 1))
  have hn0 : 0 ≤ n := by
    dsimp [n]
    positivity
  have hden : 0 < n + 1 := by linarith
  have hquot : 0 < κ / (n + 1) := div_pos hgap.1 hden
  have hε : 0 < ε := by
    exact Real.sqrt_pos.2 hquot
  have hεsq : ε ^ 2 = κ / (n + 1) := by
    exact Real.sq_sqrt hquot.le
  have hstrict : n * (κ / (n + 1)) < κ := by
    calc
      n * (κ / (n + 1)) = (n * κ) / (n + 1) := by ring
      _ < κ := by
        apply (div_lt_iff₀ hden).2
        nlinarith [hgap.1]
  have hbudget : (S.card : ℝ) * ε ^ 2 < 2 * κ := by
    change n * ε ^ 2 < 2 * κ
    rw [hεsq]
    exact hstrict.trans (by linarith [hgap.1])
  exact ⟨S, ε,
    isKazhdanPair_of_uniformLaplacianGap S hgap hε hbudget⟩

end LaplacianSOSCertificate
end GroupApproximation
