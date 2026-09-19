import Mathlib

/-!
# Diameter shrinking for iterated barycentric subdivision

This file proves the geometric *metric shrinking* facts for affine barycentric
subdivision of the standard topological simplex `Δⁿ` and its iterates.  These are
the metric inputs needed by the later small-simplices theorem (Prompt 16).

The mathematical content is the classical estimate: one barycentric subdivision
of a simplex contracts diameters by the factor `n/(n+1) < 1`, and therefore the
`N`-fold subdivision contracts by `(n/(n+1))^N → 0`.

## Design

Rather than route through the singular-chain subdivision operator, we work
directly with the affine layer.  A simplex is described by its tuple of `n+1`
vertices `V : Fin (n+1) → E` in a real normed space `E`.  One barycentric
subdivision step, for a permutation `π` of the vertices, produces the new vertex
tuple

```text
(stepVertices V π) k = barycenter {V (π 0), …, V (π k)}
                     = (k+1)⁻¹ • Σ_{j ≤ k} V (π j).
```

The geometric simplex is the convex hull of the vertex tuple, and
`Metric.diam (convexHull ℝ (Set.range V)) = Metric.diam (Set.range V)`
(`convexHull_diam`), so it suffices to bound `Metric.diam (Set.range V)`.

## Main results

* `contractionFactor n = n/(n+1)`, with `contractionFactor_nonneg` and
  `contractionFactor_lt_one`.
* `stepVertices_diam_le` — one-step contraction:
  `diam (range (stepVertices V π)) ≤ contractionFactor n * diam (range V)`.
* `iterVertices` — the vertex tuple of an affine sub-simplex of `sdᴺ`.
* `iterVertices_diam_le` — `diam (range (iterVertices …)) ≤ (contractionFactor n)^N * diam (range V)`.
* `exists_iteratedSubdivision_affine_diameter_lt` — for every `ε > 0` there is `N`
  such that *every* affine sub-simplex appearing in the `N`-fold barycentric
  subdivision of `Δⁿ` has diameter `< ε`.
-/

open scoped BigOperators
open Finset Metric

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
namespace BarycentricSubdivisionDiameter

/-! ## The contraction factor -/

/-- The dimension-dependent contraction factor `n/(n+1)`. It is `< 1` for every
`n` (in particular `0` for `n = 0`). -/
noncomputable def contractionFactor (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem contractionFactor_nonneg (n : ℕ) : 0 ≤ contractionFactor n := by
  unfold contractionFactor
  positivity

theorem contractionFactor_lt_one (n : ℕ) : contractionFactor n < 1 := by
  unfold contractionFactor
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-
Monotonicity helper: `l/(l+1) ≤ n/(n+1)` whenever `l ≤ n`.
-/
theorem ratio_le_contractionFactor {l n : ℕ} (h : l ≤ n) :
    (l : ℝ) / (l + 1) ≤ contractionFactor n := by
  rw [ contractionFactor, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## One barycentric subdivision step on a vertex tuple -/

/-- One barycentric subdivision step applied to a vertex tuple `V`, ordered by the
permutation `π`.  The `k`-th new vertex is the barycenter of the first `k+1`
old vertices in the order `π`. -/
noncomputable def stepVertices (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → E :=
  fun k => ((k.val + 1 : ℝ))⁻¹ • ∑ j ∈ Finset.Iic k, V (π j)

omit [NormedSpace ℝ E] in
/-- The range of any vertex tuple over `Fin (n+1)` is bounded. -/
theorem isBounded_range (n : ℕ) (V : Fin (n + 1) → E) :
    Bornology.IsBounded (Set.range V) :=
  (Set.finite_range V).isBounded

/-
Distance from an old vertex `V (π i)` (with `i ≤ l`) to the `l`-th new
barycenter is at most `l/(l+1)` times the diameter of the old vertex set.
-/
theorem dist_vertex_step_le (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) (l i : Fin (n + 1)) (hi : i ≤ l) :
    dist (V (π i)) (stepVertices n V π l)
      ≤ (l.val : ℝ) / (l.val + 1) * Metric.diam (Set.range V) := by
  -- By definition of $stepVertices$, we have:
  have h_step : V (π i) - (stepVertices n V π l) = (l.val + 1 : ℝ)⁻¹ • ∑ j ∈ Finset.Iic l, (V (π i) - V (π j)) := by
    simp [stepVertices];
    simp +decide [ smul_sub, ← Nat.cast_smul_eq_nsmul ℝ ];
    rw [ inv_smul_smul₀ ( Nat.cast_add_one_ne_zero _ ) ];
  have h_norm : ‖∑ j ∈ Finset.Iic l, (V (π i) - V (π j))‖ ≤ l.val * Metric.diam (Set.range V) := by
    have h_norm : ∑ j ∈ Finset.Iic l \ {i}, ‖V (π i) - V (π j)‖ ≤ l.val * Metric.diam (Set.range V) := by
      refine' le_trans ( Finset.sum_le_sum fun j hj => show ‖V ( π i ) - V ( π j )‖ ≤ Metric.diam ( Set.range V ) from _ ) _;
      · convert Metric.dist_le_diam_of_mem ( isBounded_range n V ) ( Set.mem_range_self ( π i ) ) ( Set.mem_range_self ( π j ) ) using 1 ; simp +decide [ dist_eq_norm ];
      · simp +decide [ Finset.card_sdiff, * ];
    refine' le_trans ( le_trans ( norm_sum_le _ _ ) _ ) h_norm;
    simp +decide [ Finset.sum_eq_add_sum_sdiff_singleton_of_mem ( show i ∈ Finset.Iic l from Finset.mem_Iic.mpr hi ) ];
  rw [dist_eq_norm, h_step, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (l.val + 1 : ℝ)⁻¹ * (l.val * Metric.diam (Set.range V)) :=
      mul_le_mul_of_nonneg_left h_norm (by positivity)
    _ = (l.val : ℝ) / (l.val + 1) * Metric.diam (Set.range V) := by
      rw [div_eq_mul_inv]
      ring

/-
Distance between two new barycenters `stepVertices … l` and `stepVertices … l'`
with `l ≤ l'` is at most `l'/(l'+1)` times the old diameter.
-/
theorem dist_step_step_le_aux (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) (l l' : Fin (n + 1)) (hll : l ≤ l') :
    dist (stepVertices n V π l) (stepVertices n V π l')
      ≤ (l'.val : ℝ) / (l'.val + 1) * Metric.diam (Set.range V) := by
  -- Write `D := Metric.diam (Set.range V)` and `s := Finset.Iic l`, with `s.card = l.val + 1` (`Fin.card_Iic`).
  set D := Metric.diam (Set.range V)
  set s := Finset.Iic l
  have hs : s.card = l.val + 1 := by
    simp +decide [ s ];
  -- By definition of stepVertices, we have:
  have h_step : stepVertices n V π l - stepVertices n V π l' = (l.val + 1 : ℝ)⁻¹ • ∑ i ∈ s, (V (π i) - stepVertices n V π l') := by
    simp +decide [ stepVertices, Finset.smul_sum, Finset.sum_sub_distrib, smul_sub ];
    simp +decide [ hs, ← smul_assoc ];
    grind;
  -- By definition of stepVertices, we have that for each $i \in s$, $\|V (π i) - stepVertices n V π l'\| \leq \frac{l'.val}{l'.val + 1} * D$.
  have h_dist : ∀ i ∈ s, ‖V (π i) - stepVertices n V π l'‖ ≤ (l'.val : ℝ) / (l'.val + 1) * D := by
    intro i hi; have := dist_vertex_step_le n V π l' i ( le_trans ( Finset.mem_Iic.mp hi ) hll ) ; simp_all +decide [ dist_eq_norm ] ;
    exact this;
  rw [ dist_eq_norm, h_step, norm_smul, Real.norm_of_nonneg ( by positivity ) ];
  refine' le_trans ( mul_le_mul_of_nonneg_left ( norm_sum_le _ _ ) ( by positivity ) ) _;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum h_dist ) ( by positivity ) ) _ ; simp +decide [ hs, ne_of_gt ( Nat.cast_add_one_pos _ ) ]

/-
Distance between any two new barycenters is at most `contractionFactor n`
times the old diameter.
-/
theorem dist_step_step_le (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) (l l' : Fin (n + 1)) :
    dist (stepVertices n V π l) (stepVertices n V π l')
      ≤ contractionFactor n * Metric.diam (Set.range V) := by
  rcases le_total l l' with h | h
  · exact le_trans (dist_step_step_le_aux n V π l l' h)
      (mul_le_mul_of_nonneg_right
        (ratio_le_contractionFactor (Nat.le_of_lt_succ (Fin.is_lt l'))) Metric.diam_nonneg)
  · rw [dist_comm]
    exact le_trans (dist_step_step_le_aux n V π l' l h)
      (mul_le_mul_of_nonneg_right
        (ratio_le_contractionFactor (Nat.le_of_lt_succ (Fin.is_lt l))) Metric.diam_nonneg)

/-
**One-step contraction.** One barycentric subdivision shrinks the diameter of
the vertex set by the factor `contractionFactor n`.
-/
theorem stepVertices_diam_le (n : ℕ) (V : Fin (n + 1) → E)
    (π : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (stepVertices n V π))
      ≤ contractionFactor n * Metric.diam (Set.range V) := by
  refine Metric.diam_le_of_forall_dist_le
    (mul_nonneg (contractionFactor_nonneg n) (Metric.diam_nonneg)) ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact dist_step_step_le n V π a b

/-! ## Iterated barycentric subdivision -/

/-- The vertex tuple of an affine sub-simplex appearing after `N` barycentric
subdivisions, specified by a sequence of `N` permutations `πs`. -/
noncomputable def iterVertices (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) → (Fin (n + 1) → E) →
      (Fin (n + 1) → E)
  | 0, _, V => V
  | (N + 1), πs, V =>
      stepVertices n (iterVertices n N (fun i => πs i.castSucc) V) (πs (Fin.last N))

@[simp] theorem iterVertices_zero (n : ℕ)
    (πs : Fin 0 → Equiv.Perm (Fin (n + 1))) (V : Fin (n + 1) → E) :
    iterVertices n 0 πs V = V := rfl

theorem iterVertices_succ (n N : ℕ)
    (πs : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) (V : Fin (n + 1) → E) :
    iterVertices n (N + 1) πs V
      = stepVertices n (iterVertices n N (fun i => πs i.castSucc) V) (πs (Fin.last N)) :=
  rfl

/-
**Iterated contraction.** The `N`-fold barycentric subdivision shrinks the
diameter of the vertex set by `(contractionFactor n)^N`.
-/
theorem iterVertices_diam_le (n N : ℕ)
    (πs : Fin N → Equiv.Perm (Fin (n + 1))) (V : Fin (n + 1) → E) :
    Metric.diam (Set.range (iterVertices n N πs V))
      ≤ (contractionFactor n) ^ N * Metric.diam (Set.range V) := by
  induction' N with N ih
  · simp [iterVertices]
  · rw [iterVertices_succ]
    calc
      Metric.diam (Set.range (stepVertices n
          (iterVertices n N (fun i => πs i.castSucc) V) (πs (Fin.last N))))
          ≤ contractionFactor n * Metric.diam
              (Set.range (iterVertices n N (fun i => πs i.castSucc) V)) :=
        stepVertices_diam_le n _ _
      _ ≤ contractionFactor n * ((contractionFactor n) ^ N * Metric.diam (Set.range V)) :=
        mul_le_mul_of_nonneg_left (ih _) (contractionFactor_nonneg n)
      _ = (contractionFactor n) ^ (N + 1) * Metric.diam (Set.range V) := by
        rw [pow_succ']
        ring

end Normed

/-! ## The standard simplex and the main existence theorem -/

/-- The tuple of `n+1` standard basis vertices of `Δⁿ`, as points of
`Fin (n+1) → ℝ`. -/
noncomputable def stdVerts (n : ℕ) : Fin (n + 1) → (Fin (n + 1) → ℝ) :=
  fun k => Pi.single k 1

/-
The standard vertex set has diameter at most `1`.
-/
theorem diam_range_stdVerts_le_one (n : ℕ) :
    Metric.diam (Set.range (stdVerts n)) ≤ 1 := by
  refine' le_trans ( Metric.diam_mono _ _ ) _;
  exact stdSimplex ℝ ( Fin ( n + 1 ) );
  · exact Set.range_subset_iff.mpr fun i => single_mem_stdSimplex ℝ i;
  · exact bounded_stdSimplex _
  · exact diam_stdSimplex_le

/-
**Main deliverable.** For every `ε > 0` there is a number `N` of barycentric
subdivisions such that *every* affine sub-simplex appearing in the `N`-fold
barycentric subdivision of `Δⁿ` — i.e. for every choice of the `N` permutations
`πs` — has vertex-set diameter `< ε`.
-/
theorem exists_iteratedSubdivision_affine_diameter_lt (n : ℕ) (eps : ℝ)
    (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (πs : Fin N → Equiv.Perm (Fin (n + 1))),
      Metric.diam (Set.range (iterVertices n N πs (stdVerts n))) < eps := by
  have := exists_pow_lt_of_lt_one heps ( contractionFactor_lt_one n );
  exact ⟨ this.choose, fun πs => lt_of_le_of_lt ( iterVertices_diam_le n _ _ _ ) ( lt_of_le_of_lt ( mul_le_of_le_one_right ( pow_nonneg ( contractionFactor_nonneg n ) _ ) ( diam_range_stdVerts_le_one n ) ) this.choose_spec ) ⟩

/-- Convex-hull form of the deliverable: the *geometric* affine sub-simplex (the
convex hull of the vertex tuple) has diameter `< ε` after enough subdivisions. -/
theorem exists_iteratedSubdivision_affine_convexHull_diameter_lt (n : ℕ) (eps : ℝ)
    (heps : 0 < eps) :
    ∃ N : ℕ, ∀ (πs : Fin N → Equiv.Perm (Fin (n + 1))),
      Metric.diam (convexHull ℝ (Set.range (iterVertices n N πs (stdVerts n)))) < eps := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_affine_diameter_lt n eps heps
  exact ⟨N, fun πs => by rw [convexHull_diam]; exact hN πs⟩

end BarycentricSubdivisionDiameter
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree