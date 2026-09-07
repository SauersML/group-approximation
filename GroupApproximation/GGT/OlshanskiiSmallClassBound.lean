import GroupApproximation.GGT.OlshanskiiPolygonClasses
import GroupApproximation.GGT.OlshanskiiCutPotential

/-!
# Total first-class length when a small polygon has no long pair

The contrapositive estimate keeps the desired segment length `β` unchanged.
It can therefore be added across a balanced cut: the short class is charged
eight times, and the coefficient of `β` fits the additive side-count budget.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating
open Finset

universe v
variable {X : Type v} [PseudoMetricSpace X]

theorem sum_wrapSide_tail_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    (∑ j ∈ range (n - 1), f (wrapSide n (k + 1 + j))) ≤
      ∑ j ∈ range n, f j := by
  have hfull := sum_wrapSide f hk
  have hsplit := sum_range_succ' (fun j => f (wrapSide n (k + j))) (n - 1)
  rw [show n - 1 + 1 = n by omega] at hsplit
  have ht : (∑ j ∈ range (n - 1), f (wrapSide n (k + (j + 1)))) =
      ∑ j ∈ range (n - 1), f (wrapSide n (k + 1 + j)) := by
    apply sum_congr rfl
    intro j _
    congr 2
    omega
  rw [ht, hfull] at hsplit
  have h0 := hf (wrapSide n (k + 0))
  linarith

/-- Absence of a class pair bounds each first-class side individually. -/
theorem side_length_le_of_no_classPair_small
    {δ d β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hδd : δ ≤ d) (hβ : 0 < β)
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n : ℕ}
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hpoly : IsClosedPolygonAt vs sides 0 n)
    (A B : Set ℕ) (hnone : ¬ ClassPair vs sides n A B β (12 * d))
    {k : ℕ} (hk : k < n) (hkA : k ∈ A) :
    dist (vs k) (vs (k + 1)) ≤
      ((n : ℝ) - 1) * (β + 48 * d) + classLength vs n Bᶜ := by
  classical
  by_contra hbad
  have hlong := lt_of_not_ge hbad
  let w : ℕ → ℝ := fun i =>
    if wrapSide n i ∈ B then 0 else
      dist (vs (wrapSide n i)) (vs (wrapSide n i + 1))
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> positivity
  have hclose : vs n = vs 0 := by simpa only [zero_add] using hpoly.2
  have hrot := isClosedPolygonAt_rotate hpoly (show 0 ≤ k by omega)
    (show k ≤ 0 + n by omega)
  have hshort : ∀ i, k < i → i < k + n → i ∉ (wrapSide n ⁻¹' B) →
      dist (rotVertex vs n 0 i) (rotVertex vs n 0 (i + 1)) ≤ w i := by
    intro i _ _ hi
    change wrapSide n i ∉ B at hi
    simp only [rotVertex_dist_eq_wrap hclose, w, if_neg hi, le_refl]
  have htotal : (∑ j ∈ range (n - 1), w (k + 1 + j)) ≤
      classLength vs n Bᶜ := by
    have h := sum_wrapSide_tail_le
      (fun i => if i ∈ B then 0 else dist (vs i) (vs (i + 1)))
      (fun i => by split_ifs <;> positivity) (show 1 ≤ n by omega) (le_of_lt hk)
    simpa only [w, classLength, Set.mem_compl_iff, ite_not] using h
  have hlong' : ((n : ℝ) - 1) * (β + 4 * (12 * d)) + classLength vs n Bᶜ <
      dist (rotVertex vs n 0 k) (rotVertex vs n 0 (k + 1)) := by
    rw [rotVertex_dist_eq_wrap hclose]
    simpa only [wrapSide, if_pos hk, show 4 * (12 * d) = 48 * d by ring] using hlong
  obtain ⟨i, hki, hin, hiB, u, hu, u', hu', t, ht, t', ht', hlen, hlen', hc, hc'⟩ :=
    exists_long_close_pair hδ hδ0 hgeo hn (c := 3) (by omega) hrot
      (by norm_num; linarith) (wrapSide n ⁻¹' B) w hw hshort htotal hβ hlong'
  have hp : SidePair (rotVertex vs n 0) (rotSide sides n 0) k i β (12 * d) := by
    refine ⟨u, hu, u', hu', t, ht, t', ht', le_trans hlen (le_abs_self _),
      hlen', hc, hc'⟩
  have hp' := hp.of_rotation hclose
  have hwrap : wrapSide n k = k := by simp only [wrapSide, if_pos hk]
  rw [hwrap] at hp'
  apply hnone
  refine ⟨k, hk, wrapSide n i, wrapSide_lt hk hin, hkA, hiB, ?_, hp'⟩
  intro heq
  have heq' : wrapSide n k = wrapSide n i := hwrap.trans heq
  have := wrapSide_injective (le_refl k) (by omega : k < k + n)
    (le_of_lt hki) hin heq'
  omega

/-- The base estimate that adds across cuts, with no rescaling of `β`. -/
theorem classLength_le_of_no_classPair_small
    {δ d β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hδd : δ ≤ d) (hβ : 0 < β)
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n : ℕ}
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hpoly : IsClosedPolygonAt vs sides 0 n)
    (A B : Set ℕ) (hnone : ¬ ClassPair vs sides n A B β (12 * d)) :
    classLength vs n A ≤ 8 * classLength vs n Bᶜ +
      (n : ℝ) * ((n : ℝ) - 1) * β + 48 * n * ((n : ℝ) - 1) * d := by
  classical
  have hd : 0 ≤ d := hδ0.trans hδd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hshort := classLength_nonneg vs n Bᶜ
  have hC : 0 ≤ ((n : ℝ) - 1) * (β + 48 * d) + classLength vs n Bᶜ := by positivity
  have hsum : classLength vs n A ≤
      (n : ℝ) * (((n : ℝ) - 1) * (β + 48 * d) + classLength vs n Bᶜ) := by
    unfold classLength
    calc
      _ ≤ ∑ _i ∈ range n,
          (((n : ℝ) - 1) * (β + 48 * d) + classLength vs n Bᶜ) := by
        apply sum_le_sum
        intro i hi
        by_cases hiA : i ∈ A
        · rw [if_pos hiA]
          exact side_length_le_of_no_classPair_small hδ hδ0 hgeo hδd hβ hn hn8
            hpoly A B hnone (mem_range.mp hi) hiA
        · rw [if_neg hiA]
          exact hC
      _ = _ := by simp [classLength, mul_add]
  have hnR : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
  have hscale := mul_le_mul_of_nonneg_right hnR hshort
  nlinarith

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.side_length_le_of_no_classPair_small
#audit_axioms GroupApproximation.Olshanskii.classLength_le_of_no_classPair_small
