import GroupApproximation.Analysis.GroupHilbertSubsetProjection
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.OrthogonalProjectionSumEstimate

/-!
# Powers' averaging estimate from a partition of the group

This module proves the analytic core of Powers' theorem — component (C) of
`Analysis/PowersAveraging`, which that module names and does not prove — **from
a purely combinatorial input**: a partition `G = C ⊔ D` and averaging elements
`g₁, …, gₙ` whose translates `gᵢ D` are pairwise disjoint.

## The estimate

`norm_average_le_of_partition`.  Let `a` be a bounded operator on `ℓ²(G)` with

    P_C a P_C = 0,

let `G = C ⊔ D`, and let `g₁, …, gₙ` have the `gᵢ D` pairwise disjoint.  Then

    ‖ (1/n) ∑ᵢ λ(gᵢ) a λ(gᵢ)⋆ ‖ ≤ 2‖a‖ / √n.

## The argument

Write `P = P_C` and `Q = P_D`, so `P + Q = 1`.  Expanding `a = (P+Q) a (P+Q)`
and deleting `P a P` gives

    a = a Q + Q a P.

Conjugating by `λ(gᵢ)` and using `λ(g) Q λ(g)⋆ = P_{g D}`
(`leftRegularOperator_conj_subsetProjection`) turns the `i`-th summand into

    Aᵢ Qᵢ + Qᵢ Bᵢ,   Aᵢ = λ(gᵢ) a λ(gᵢ)⋆,  Bᵢ = λ(gᵢ) a P λ(gᵢ)⋆,  Qᵢ = P_{gᵢ D}.

The `Qᵢ` are self-adjoint of norm at most one and pairwise orthogonal, because
the `gᵢ D` are pairwise disjoint.  So both sums are bounded by `√n ‖a‖`
(`ShulmanFill.norm_sum_mul_projection_le` and its mirror), the total is
`2√n ‖a‖`, and dividing by `n` gives `2‖a‖/√n`.

## Why the projections need not lie in `C*_r(G)`

They do not, and nothing here asks them to: the whole computation happens in
`B(ℓ²G)`.  The reduced C⋆-algebra enters only when a consumer restricts the
conclusion along the isometric inclusion of `C*_r(G)` into `B(ℓ²G)`.

## What is still missing for Powers' theorem

Exactly the combinatorics: a group for which such partitions exist for every
finite `F ⊆ G \ {1}` and every `n` — the *Powers property*.  For a free group of
rank at least two this is a statement about reduced words and is not proved
here.  `subsetProjection_conj_eq_zero_of_disjoint` below is the bridge that
turns `f C ∩ C = ∅` into the hypothesis `P_C λ(f) P_C = 0`, so a producer of the
combinatorics meets this module at a purely set-theoretic interface.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open GroupApproximation.GroupVonNeumann
open scoped Pointwise

universe u

noncomputable section

variable (G : Type u) [Group G]

/-! ## The unitaries `λ(g)` -/

theorem star_leftRegularOperator_mul_self (g : G) :
    star (leftRegularOperator G g) * leftRegularOperator G g = 1 := by
  rw [star_leftRegularOperator, leftRegularOperator_mul, inv_mul_cancel,
    leftRegularOperator_one]

theorem leftRegularOperator_mul_star_self (g : G) :
    leftRegularOperator G g * star (leftRegularOperator G g) = 1 := by
  rw [star_leftRegularOperator, leftRegularOperator_mul, mul_inv_cancel,
    leftRegularOperator_one]

/-! ## `P_C + P_D = 1` for a partition

The contraction bound `‖λ(g)‖ ≤ 1` is the landed
`ReducedGroupCStarTrace.norm_leftRegularOperator_le_one` of
`Analysis/ReducedGroupCStarSpan`, not a copy. -/

/-- **A partition of the group gives complementary projections.** -/
theorem subsetProjection_add_of_partition {C D : Set G} (hdisj : Disjoint C D)
    (hunion : C ∪ D = Set.univ) :
    subsetProjection G C + subsetProjection G D = 1 := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    subsetProjection_apply, subsetProjection_apply]
  have hg : g ∈ C ∪ D := by rw [hunion]; exact Set.mem_univ g
  rcases hg with hC | hD
  · have hnD : g ∉ D := Set.disjoint_left.mp hdisj hC
    rw [indicatorSymbol_of_mem G hC, indicatorSymbol_of_notMem G hnD, one_mul,
      zero_mul, add_zero]
  · have hnC : g ∉ C := Set.disjoint_right.mp hdisj hD
    rw [indicatorSymbol_of_notMem G hnC, indicatorSymbol_of_mem G hD, one_mul,
      zero_mul, zero_add]

/-! ## The set-theoretic interface -/

/-- **`λ(g) P_S = P_{gS} λ(g)`.** -/
theorem leftRegularOperator_mul_subsetProjection (g : G) (S : Set G) :
    leftRegularOperator G g * subsetProjection G S
      = subsetProjection G (g • S) * leftRegularOperator G g := by
  calc leftRegularOperator G g * subsetProjection G S
      = leftRegularOperator G g * subsetProjection G S *
          (star (leftRegularOperator G g) * leftRegularOperator G g) := by
        rw [star_leftRegularOperator_mul_self, mul_one]
    _ = leftRegularOperator G g * subsetProjection G S *
          star (leftRegularOperator G g) * leftRegularOperator G g := by
        rw [mul_assoc]
    _ = subsetProjection G (g • S) * leftRegularOperator G g := by
        rw [leftRegularOperator_conj_subsetProjection]

/-- **`f C ∩ C = ∅` gives `P_C λ(f) P_C = 0`.**

This is the bridge from Powers' combinatorial condition to the algebraic
hypothesis of the estimate. -/
theorem subsetProjection_conj_eq_zero_of_disjoint {C : Set G} {f : G}
    (h : Disjoint (f • C) C) :
    subsetProjection G C * leftRegularOperator G f * subsetProjection G C = 0 := by
  rw [mul_assoc, leftRegularOperator_mul_subsetProjection, ← mul_assoc,
    subsetProjection_mul_of_disjoint G (h.symm), zero_mul]

/-! ## The estimate -/

/-- **Powers' averaging estimate from a partition.**

`P_C a P_C = 0`, `G = C ⊔ D`, and pairwise disjoint translates `gᵢ D` give

    ‖ (1/n) ∑ᵢ λ(gᵢ) a λ(gᵢ)⋆ ‖ ≤ 2‖a‖ / √n. -/
theorem norm_average_le_of_partition
    (a : GroupHilbert G →L[ℂ] GroupHilbert G) {C D : Set G}
    (hdisj : Disjoint C D) (hunion : C ∪ D = Set.univ)
    (hPaP : subsetProjection G C * a * subsetProjection G C = 0)
    {n : ℕ} (hn : 0 < n) (g : Fin n → G)
    (hg : ∀ i j, i ≠ j → Disjoint (g i • D) (g j • D)) :
    ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
        leftRegularOperator G (g i) * a * star (leftRegularOperator G (g i))‖
      ≤ 2 * ‖a‖ / Real.sqrt n := by
  set 𝔅 := GroupHilbert G →L[ℂ] GroupHilbert G
  set P : 𝔅 := subsetProjection G C with hP
  set Q : 𝔅 := subsetProjection G D with hQ
  -- `a = a Q + Q a P`.
  have hsplit : a = a * Q + Q * a * P := by
    have hPQ : P + Q = 1 := subsetProjection_add_of_partition G hdisj hunion
    have expand : (P + Q) * a * (P + Q)
        = (P + Q) * a * Q + Q * a * P + P * a * P := by
      simp only [add_mul, mul_add, mul_assoc]
      abel
    have hlhs : (P + Q) * a * (P + Q) = a := by rw [hPQ, one_mul, mul_one]
    have hrhs : (P + Q) * a * Q = a * Q := by rw [hPQ, one_mul]
    rw [hlhs, hrhs, hPaP, add_zero] at expand
    exact expand
  -- The three families.
  set A : Fin n → 𝔅 := fun i ↦
    leftRegularOperator G (g i) * a * star (leftRegularOperator G (g i)) with hA
  set B : Fin n → 𝔅 := fun i ↦
    leftRegularOperator G (g i) * (a * P) * star (leftRegularOperator G (g i)) with hB
  set R : Fin n → 𝔅 := fun i ↦ subsetProjection G (g i • D) with hR
  -- The `Rᵢ` are pairwise orthogonal self-adjoint contractions.
  have hRstar : ∀ i, star (R i) = R i := fun i ↦ subsetProjection_star G _
  have hRnorm : ∀ i, ‖R i‖ ≤ 1 := fun i ↦ norm_subsetProjection_le_one G _
  have hRorth : ∀ i j, i ≠ j → R i * R j = 0 := fun i j hij ↦
    subsetProjection_mul_of_disjoint G (hg i j hij)
  -- Norm bounds on `A` and `B`.
  have hconj : ∀ (x : 𝔅) (i : Fin n),
      ‖leftRegularOperator G (g i) * x * star (leftRegularOperator G (g i))‖ ≤ ‖x‖ := by
    intro x i
    have h1 : ‖leftRegularOperator G (g i) * x * star (leftRegularOperator G (g i))‖
        ≤ ‖leftRegularOperator G (g i) * x‖ * ‖star (leftRegularOperator G (g i))‖ :=
      norm_mul_le _ _
    have h2 : ‖leftRegularOperator G (g i) * x‖ ≤ ‖leftRegularOperator G (g i)‖ * ‖x‖ :=
      norm_mul_le _ _
    have h3 : ‖star (leftRegularOperator G (g i))‖ ≤ 1 := by
      rw [norm_star]
      exact norm_leftRegularOperator_le_one G (g i)
    nlinarith [norm_nonneg x, norm_nonneg (leftRegularOperator G (g i)),
      norm_nonneg (leftRegularOperator G (g i) * x),
      norm_leftRegularOperator_le_one G (g i), h1, h2, h3]
  have hAnorm : ∀ i, ‖A i‖ ≤ ‖a‖ := fun i ↦ hconj a i
  have hBnorm : ∀ i, ‖B i‖ ≤ ‖a‖ := by
    intro i
    refine (hconj (a * P) i).trans ?_
    calc ‖a * P‖ ≤ ‖a‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ ‖a‖ * 1 := by
          have := norm_subsetProjection_le_one G C
          nlinarith [norm_nonneg a]
      _ = ‖a‖ := mul_one _
  -- The summand identity.
  have hterm : ∀ i, A i = A i * R i + R i * B i := by
    intro i
    have hRi : R i = leftRegularOperator G (g i) * Q *
        star (leftRegularOperator G (g i)) := by
      rw [hR, hQ, leftRegularOperator_conj_subsetProjection]
    have hvu : ∀ X : 𝔅, star (leftRegularOperator G (g i)) *
        (leftRegularOperator G (g i) * X) = X := by
      intro X
      rw [← mul_assoc, star_leftRegularOperator_mul_self, one_mul]
    rw [hRi, hA, hB]
    calc leftRegularOperator G (g i) * a * star (leftRegularOperator G (g i))
        = leftRegularOperator G (g i) * ((a * Q + Q * a * P) *
            star (leftRegularOperator G (g i))) := by
          rw [← hsplit, mul_assoc]
      _ = leftRegularOperator G (g i) * (a * (Q * star (leftRegularOperator G (g i))))
          + leftRegularOperator G (g i) *
            (Q * (a * (P * star (leftRegularOperator G (g i))))) := by
          simp only [add_mul, mul_add, mul_assoc]
      _ = _ := by
          rw [show leftRegularOperator G (g i) * a * star (leftRegularOperator G (g i)) *
                (leftRegularOperator G (g i) * Q * star (leftRegularOperator G (g i)))
              = leftRegularOperator G (g i) * (a *
                  (star (leftRegularOperator G (g i)) *
                    (leftRegularOperator G (g i) *
                      (Q * star (leftRegularOperator G (g i)))))) by
              simp only [mul_assoc],
            hvu,
            show leftRegularOperator G (g i) * Q * star (leftRegularOperator G (g i)) *
                (leftRegularOperator G (g i) * (a * P) *
                  star (leftRegularOperator G (g i)))
              = leftRegularOperator G (g i) * (Q *
                  (star (leftRegularOperator G (g i)) *
                    (leftRegularOperator G (g i) *
                      (a * (P * star (leftRegularOperator G (g i))))))) by
              simp only [mul_assoc],
            hvu]
  -- Split the sum.
  have hsum : ∑ i : Fin n, A i = (∑ i : Fin n, A i * R i) + ∑ i : Fin n, R i * B i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hterm i
  -- Bound each half.
  have hnorma : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  have h1 : ‖∑ i : Fin n, A i * R i‖ ≤ Real.sqrt n * ‖a‖ :=
    ShulmanFill.norm_sum_mul_projection_le A R ‖a‖ hnorma hAnorm hRnorm hRstar hRorth
  have h2 : ‖∑ i : Fin n, R i * B i‖ ≤ Real.sqrt n * ‖a‖ :=
    ShulmanFill.norm_sum_projection_mul_le B R ‖a‖ hnorma hBnorm hRnorm hRstar hRorth
  have htotal : ‖∑ i : Fin n, A i‖ ≤ 2 * (Real.sqrt n * ‖a‖) := by
    rw [hsum]
    calc ‖(∑ i : Fin n, A i * R i) + ∑ i : Fin n, R i * B i‖
        ≤ ‖∑ i : Fin n, A i * R i‖ + ‖∑ i : Fin n, R i * B i‖ := norm_add_le _ _
      _ ≤ Real.sqrt n * ‖a‖ + Real.sqrt n * ‖a‖ := add_le_add h1 h2
      _ = 2 * (Real.sqrt n * ‖a‖) := by ring
  -- Divide by `n`.
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hnormsmul : ‖(n : ℂ)⁻¹ • ∑ i : Fin n, A i‖ = (n : ℝ)⁻¹ * ‖∑ i : Fin n, A i‖ := by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
  rw [hnormsmul]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
    (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  have hfinal : (n : ℝ)⁻¹ * (2 * (Real.sqrt n * ‖a‖)) = 2 * ‖a‖ / Real.sqrt n := by
    rw [hcast]
    field_simp
    ring
  calc (n : ℝ)⁻¹ * ‖∑ i : Fin n, A i‖
      ≤ (n : ℝ)⁻¹ * (2 * (Real.sqrt n * ‖a‖)) := by
        exact mul_le_mul_of_nonneg_left htotal (le_of_lt (inv_pos.mpr hnpos))
    _ = 2 * ‖a‖ / Real.sqrt n := hfinal

/-! ## The same estimate inside the reduced C⋆-algebra

`PowersAveragingEstimate` is a statement about `C*_r(G)`, and the projections
are not in `C*_r(G)`.  The bridge is that `C*_r(G)` is a star subalgebra of
`B(ℓ²G)` carrying the induced norm, so the average may be computed either side
of the inclusion. -/

/-- The norm of the reduced C⋆-algebra is the ambient operator norm. -/
theorem norm_coe_reducedGroupCStar (x : ReducedGroupCStar G) :
    ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G)‖ = ‖x‖ := rfl

/-- The average computed in `C*_r(G)` is the average computed in `B(ℓ²G)`. -/
theorem coe_reducedAverageSum (a : ReducedGroupCStar G) (n : ℕ) (g : Fin n → G) :
    ((∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)) :
          ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G)
      = ∑ i : Fin n, leftRegularOperator G (g i) *
          (a : GroupHilbert G →L[ℂ] GroupHilbert G) *
          star (leftRegularOperator G (g i)) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, StarMemClass.coe_star]

/-- **Powers' averaging estimate from a partition, inside `C*_r(G)`.**

The hypothesis `P_C a P_C = 0` is still stated in `B(ℓ²G)`, because that is
where the projections live; everything else is the reduced algebra's own
vocabulary, and this is the form `PowersAveragingEstimate` consumes. -/
theorem norm_reducedAverage_le_of_partition (a : ReducedGroupCStar G) {C D : Set G}
    (hdisj : Disjoint C D) (hunion : C ∪ D = Set.univ)
    (hPaP : subsetProjection G C * (a : GroupHilbert G →L[ℂ] GroupHilbert G) *
      subsetProjection G C = 0)
    {n : ℕ} (hn : 0 < n) (g : Fin n → G)
    (hg : ∀ i j, i ≠ j → Disjoint (g i • D) (g j • D)) :
    ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))‖
      ≤ 2 * ‖a‖ / Real.sqrt n := by
  have hsum : ‖(∑ i : Fin n, reducedLeftRegular G (g i) * a *
        star (reducedLeftRegular G (g i)) : ReducedGroupCStar G)‖
      = ‖∑ i : Fin n, leftRegularOperator G (g i) *
          (a : GroupHilbert G →L[ℂ] GroupHilbert G) *
          star (leftRegularOperator G (g i))‖ := by
    rw [← coe_reducedAverageSum, norm_coe_reducedGroupCStar]
  have hmain := norm_average_le_of_partition G
    (a : GroupHilbert G →L[ℂ] GroupHilbert G) hdisj hunion hPaP hn g hg
  rw [norm_smul, norm_coe_reducedGroupCStar] at hmain
  rw [norm_smul, hsum]
  exact hmain

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms norm_coe_reducedGroupCStar
#audit_axioms coe_reducedAverageSum
#audit_axioms norm_reducedAverage_le_of_partition
#audit_axioms subsetProjection_add_of_partition
#audit_axioms leftRegularOperator_mul_subsetProjection
#audit_axioms subsetProjection_conj_eq_zero_of_disjoint
#audit_axioms norm_average_le_of_partition
