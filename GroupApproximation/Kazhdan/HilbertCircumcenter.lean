import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Chebyshev center of a bounded set in a Hilbert space

Every nonempty bounded subset of a complete real inner product space has
a unique circumcenter: the unique minimizer of the supremal distance to
the set.  The parallelogram law makes the covering radius function
uniformly convex, so minimizing sequences are Cauchy and the minimizer is
unique.  This is the fixed-point engine behind the Delorme direction of
the Delorme–Guichardet theorem: an affine isometric action with a bounded
orbit fixes the circumcenter of that orbit.
-/

namespace GroupApproximation
namespace Circumcenter

variable {E : Type*} [NormedAddCommGroup E]

/-- The covering radius of a set from a point. -/
noncomputable def coveringRadius (S : Set E) (x : E) : ℝ :=
  sSup ((fun s ↦ dist x s) '' S)

theorem dist_le_coveringRadius {S : Set E} (hbdd : Bornology.IsBounded S)
    (x : E) {s : E} (hs : s ∈ S) : dist x s ≤ coveringRadius S x := by
  refine le_csSup ?_ ⟨s, hs, rfl⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hbdd
  exact ⟨R, by
    rintro _ ⟨t, ht, rfl⟩
    exact Metric.mem_closedBall'.mp (hR ht)⟩

theorem coveringRadius_le {S : Set E} (hne : S.Nonempty) {x : E} {r : ℝ}
    (h : ∀ s ∈ S, dist x s ≤ r) : coveringRadius S x ≤ r := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

theorem coveringRadius_nonneg {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x : E) :
    0 ≤ coveringRadius S x := by
  obtain ⟨s, hs⟩ := hne
  exact le_trans dist_nonneg (dist_le_coveringRadius hbdd x hs)

theorem coveringRadius_lipschitz {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x y : E) :
    coveringRadius S x ≤ coveringRadius S y + dist x y := by
  apply coveringRadius_le hne
  intro s hs
  calc
    dist x s ≤ dist x y + dist y s := dist_triangle x y s
    _ ≤ dist x y + coveringRadius S y :=
      add_le_add le_rfl (dist_le_coveringRadius hbdd y hs)
    _ = coveringRadius S y + dist x y := by ring

section

variable [InnerProductSpace ℝ E]

/-- The parallelogram estimate for covering radii: the radius at a
midpoint improves quadratically in the separation. -/
theorem coveringRadius_midpoint_sq {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x y : E) :
    coveringRadius S (midpoint ℝ x y) ^ 2 + dist x y ^ 2 / 4 ≤
      (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 := by
  have hmid : ∀ s ∈ S, dist (midpoint ℝ x y) s ^ 2 ≤
      (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 -
        dist x y ^ 2 / 4 := by
    intro s hs
    have hpar := parallelogram_law_with_norm ℝ (x - s) (y - s)
    have hxs : dist x s ≤ coveringRadius S x :=
      dist_le_coveringRadius hbdd x hs
    have hys : dist y s ≤ coveringRadius S y :=
      dist_le_coveringRadius hbdd y hs
    have hmids : dist (midpoint ℝ x y) s =
        ‖(x - s) + (y - s)‖ / 2 := by
      rw [dist_eq_norm]
      rw [show midpoint ℝ x y - s =
          (2 : ℝ)⁻¹ • ((x - s) + (y - s)) from by
        rw [midpoint_eq_smul_add, invOf_eq_inv]
        module]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      ring
    have hd : dist x y = ‖(x - s) - (y - s)‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    have hx' : ‖x - s‖ = dist x s := (dist_eq_norm x s).symm
    have hy' : ‖y - s‖ = dist y s := (dist_eq_norm y s).symm
    have hxsq : dist x s ^ 2 ≤ coveringRadius S x ^ 2 :=
      pow_le_pow_left₀ dist_nonneg hxs 2
    have hysq : dist y s ^ 2 ≤ coveringRadius S y ^ 2 :=
      pow_le_pow_left₀ dist_nonneg hys 2
    have hxn : ‖x - s‖ ^ 2 ≤ coveringRadius S x ^ 2 := by
      rw [hx']
      exact hxsq
    have hyn : ‖y - s‖ ^ 2 ≤ coveringRadius S y ^ 2 := by
      rw [hy']
      exact hysq
    rw [hmids]
    rw [div_pow]
    rw [hd]
    nlinarith only [hpar, hxn, hyn, sq_nonneg (dist x y)]
  have h2 : coveringRadius S (midpoint ℝ x y) ^ 2 ≤
      (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 -
        dist x y ^ 2 / 4 := by
    have hrad0 : 0 ≤ coveringRadius S (midpoint ℝ x y) :=
      coveringRadius_nonneg hne hbdd _
    have hbound : coveringRadius S (midpoint ℝ x y) ≤
        Real.sqrt ((coveringRadius S x ^ 2 +
          coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4) := by
      apply coveringRadius_le hne
      intro s hs
      have := hmid s hs
      calc
        dist (midpoint ℝ x y) s =
            Real.sqrt (dist (midpoint ℝ x y) s ^ 2) := by
          rw [Real.sqrt_sq dist_nonneg]
        _ ≤ Real.sqrt ((coveringRadius S x ^ 2 +
            coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4) :=
          Real.sqrt_le_sqrt this
    have hsqrtnn : (0 : ℝ) ≤ (coveringRadius S x ^ 2 +
        coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4 := by
      obtain ⟨s, hs⟩ := hne
      nlinarith only [hmid s hs, sq_nonneg (dist (midpoint ℝ x y) s)]
    calc
      coveringRadius S (midpoint ℝ x y) ^ 2 ≤
          Real.sqrt ((coveringRadius S x ^ 2 +
            coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4) ^ 2 :=
        pow_le_pow_left₀ hrad0 hbound 2
      _ = (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 -
          dist x y ^ 2 / 4 := Real.sq_sqrt hsqrtnn
  linarith only [h2]

end

/-- The Chebyshev radius of a set. -/
noncomputable def chebyshevRadius (S : Set E) : ℝ :=
  ⨅ x : E, coveringRadius S x

theorem coveringRadius_bddBelow (S : Set E) (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) :
    BddBelow (Set.range (coveringRadius S)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact coveringRadius_nonneg hne hbdd y

theorem chebyshevRadius_le {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x : E) :
    chebyshevRadius S ≤ coveringRadius S x :=
  ciInf_le (coveringRadius_bddBelow S hne hbdd) x

theorem exists_coveringRadius_lt {S : Set E} (hE : Nonempty E) {r : ℝ}
    (hr : chebyshevRadius S < r) :
    ∃ x : E, coveringRadius S x < r := by
  haveI := hE
  by_contra hall
  push Not at hall
  have hge : r ≤ chebyshevRadius S := le_ciInf hall
  exact (not_lt_of_ge hge) hr

section

variable [InnerProductSpace ℝ E]

/-- **Existence and uniqueness of the Chebyshev center** of a nonempty
bounded set in a complete real inner product space. -/
theorem existsUnique_center [CompleteSpace E] {S : Set E}
    (hne : S.Nonempty) (hbdd : Bornology.IsBounded S) :
    ∃! c : E, coveringRadius S c = chebyshevRadius S := by
  obtain ⟨s₀, hs₀⟩ := id hne
  haveI : Nonempty E := ⟨s₀⟩
  set ρ := chebyshevRadius S with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, chebyshevRadius]
    exact le_ciInf fun x ↦ coveringRadius_nonneg hne hbdd x
  have hseq : ∀ n : ℕ, ∃ x : E,
      coveringRadius S x < ρ + 1 / (n + 1) := by
    intro n
    apply exists_coveringRadius_lt ⟨s₀⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lt_add_of_pos_right ρ hpos
  choose x hx using hseq
  have hsep : ∀ y z : E, dist y z ^ 2 ≤
      2 * coveringRadius S y ^ 2 + 2 * coveringRadius S z ^ 2 -
        4 * ρ ^ 2 := by
    intro y z
    have hmid := coveringRadius_midpoint_sq hne hbdd y z
    have hmin : ρ ≤ coveringRadius S (midpoint ℝ y z) :=
      chebyshevRadius_le hne hbdd _
    have hmidnn : 0 ≤ coveringRadius S (midpoint ℝ y z) :=
      coveringRadius_nonneg hne hbdd _
    nlinarith only [hmid, hmin, hmidnn, hρ0]
  have hdist_sq : ∀ m n : ℕ, dist (x m) (x n) ^ 2 ≤
      8 * (ρ + 1) * (1 / (m + 1) + 1 / (n + 1)) := by
    intro m n
    have h1 := hsep (x m) (x n)
    have h2 := (hx m).le
    have h3 := (hx n).le
    have h4 : 0 ≤ coveringRadius S (x m) :=
      coveringRadius_nonneg hne hbdd _
    have h5 : 0 ≤ coveringRadius S (x n) :=
      coveringRadius_nonneg hne hbdd _
    have hm1 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hn1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hm2 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
    have hn2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    nlinarith only [h1, h2, h3, h4, h5, hm1, hn1, hm2, hn2, hρ0]
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (16 * (ρ + 1) / ε ^ 2)
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    have hm1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith only [this]
    have hn1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith only [this]
    have hd := hdist_sq n m
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hkey : 16 * (ρ + 1) / ((N : ℝ) + 1) < ε ^ 2 := by
      rw [div_lt_iff₀ hNpos]
      have h16 : (0 : ℝ) < 16 * (ρ + 1) := by positivity
      have hN2 : 16 * (ρ + 1) / ε ^ 2 < (N : ℝ) := hN
      have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
      rw [div_lt_iff₀ hε2] at hN2
      nlinarith only [hN2, h16, hε2]
    have hd2 : dist (x n) (x m) ^ 2 < ε ^ 2 := by
      calc
        dist (x n) (x m) ^ 2 ≤
            8 * (ρ + 1) * (1 / (n + 1) + 1 / (m + 1)) := hd
        _ ≤ 8 * (ρ + 1) * (2 / ((N : ℝ) + 1)) := by
          have : 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤
              2 / ((N : ℝ) + 1) := by
            rw [show (2 : ℝ) / ((N : ℝ) + 1) =
              1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) by ring]
            linarith only [hm1, hn1]
          exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = 16 * (ρ + 1) / ((N : ℝ) + 1) := by ring
        _ < ε ^ 2 := hkey
    nlinarith only [hd2, dist_nonneg (x := x n) (y := x m), hε]
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hrc : coveringRadius S c = ρ := by
    apply le_antisymm
    · by_contra hgt
      push Not at hgt
      set η := coveringRadius S c - ρ with hη
      have hηpos : 0 < η := by
        rw [hη]
        exact sub_pos.mpr hgt
      obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < η / 2 ∧
          dist c (x n) < η / 2 := by
        obtain ⟨n₁, hn₁⟩ := exists_nat_gt (2 / η)
        have hd := Metric.tendsto_atTop.1 hc (η / 2) (by positivity)
        obtain ⟨n₂, hn₂⟩ := hd
        refine ⟨max n₁ n₂, ?_, ?_⟩
        · have hle : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
            exact_mod_cast le_max_left n₁ n₂
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hηpos] at hn₁
          nlinarith only [hn₁, hle, hηpos]
        · rw [dist_comm]
          exact hn₂ (max n₁ n₂) (le_max_right n₁ n₂)
      have : coveringRadius S c ≤ ρ + 1 / (n + 1) + dist c (x n) := by
        calc
          coveringRadius S c ≤ coveringRadius S (x n) + dist c (x n) :=
            coveringRadius_lipschitz hne hbdd c (x n)
          _ ≤ ρ + 1 / (n + 1) + dist c (x n) := by
            linarith only [hx n]
      rw [hη] at hηpos hn1
      linarith only [this, hn1, hn2, hηpos]
    · exact chebyshevRadius_le hne hbdd c
  refine ⟨c, hrc, ?_⟩
  intro c' hc'
  have hd := hsep c' c
  rw [hrc, hc'] at hd
  have : dist c' c ^ 2 ≤ 0 := by nlinarith only [hd]
  have : dist c' c = 0 := by
    nlinarith only [this, dist_nonneg (x := c') (y := c)]
  exact dist_eq_zero.1 this

end

/-- Covering radii transform along isometries. -/
theorem coveringRadius_image {f : E → E} (hf : Isometry f)
    (S : Set E) (x : E) :
    coveringRadius (f '' S) (f x) = coveringRadius S x := by
  unfold coveringRadius
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, (hf.dist_eq x s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨f s, ⟨s, hs, rfl⟩, hf.dist_eq x s⟩

end Circumcenter
end GroupApproximation
