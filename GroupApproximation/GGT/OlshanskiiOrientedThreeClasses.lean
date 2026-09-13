import GroupApproximation.GGT.OlshanskiiOrientedBisection
import GroupApproximation.GGT.OlshanskiiOrientedLemma25
import GroupApproximation.GGT.OlshanskiiSmallClassBound

/-!
# Ol'shanskii's three-class polygon lemma with antiparallel pairs

`OlshanskiiThreeClasses` proves the three-class lemma (Osin's Lemma 3.7) with an
unoriented `ClassPair`. Osin's planar Case 1 needs the two fellow-travelling
segments to be antiparallel. This module proves the same statement with
`OrientedClassPair`, with the same constants `12(δ+1)` and `100000(δ+1)`.

The proof is the one of `OlshanskiiThreeClasses`, with two substitutions. On
polygons with at most eight sides, `exists_long_antiparallel_pair` replaces
`exists_long_close_pair`; it applies at `c = 3` because `n ≤ 8 = 2 ^ 3`. The
induction step cuts with `exists_orientedClassifiedBisection`, whose children
lift antiparallel pairs.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.VanKampen.Estimating
open Finset

universe v
variable {X : Type v} [PseudoMetricSpace X]

/-- Absence of an antiparallel class pair bounds each first-class side. -/
theorem side_length_le_of_no_orientedClassPair_small
    {δ d β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hδd : δ ≤ d) (hβ : 0 < β)
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n : ℕ}
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hpoly : IsClosedPolygonAt vs sides 0 n)
    (A B : Set ℕ) (hnone : ¬ OrientedClassPair vs sides n A B β (12 * d))
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
    exists_long_antiparallel_pair hδ hδ0 hgeo hn (c := 3) (by omega) hrot
      (by norm_num; linarith) (wrapSide n ⁻¹' B) w hw hshort htotal hβ hlong'
  have hp : OrientedSidePair (rotVertex vs n 0) (rotSide sides n 0) k i β (12 * d) :=
    ⟨u, hu, u', hu', t, ht, t', ht', hlen, hlen', hc, hc'⟩
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
theorem classLength_le_of_no_orientedClassPair_small
    {δ d β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hδd : δ ≤ d) (hβ : 0 < β)
    {vs : ℕ → X} {sides : ℕ → ℝ → X} {n : ℕ}
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hpoly : IsClosedPolygonAt vs sides 0 n)
    (A B : Set ℕ) (hnone : ¬ OrientedClassPair vs sides n A B β (12 * d)) :
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
          exact side_length_le_of_no_orientedClassPair_small hδ hδ0 hgeo hδd hβ hn hn8
            hpoly A B hnone (mem_range.mp hi) hiA
        · rw [if_neg hiA]
          exact hC
      _ = _ := by simp [classLength, mul_add]
  have hnR : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
  have hscale := mul_le_mul_of_nonneg_right hnR hshort
  nlinarith

private theorem beta_cost_of_le_eight {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    (n : ℝ) * ((n : ℝ) - 1) ≤ 20 * (n - 4 : ℕ) := by
  interval_cases n <;> norm_num

/-- The induction of `classLength_le_of_no_classPair`, for antiparallel pairs. -/
theorem classLength_le_of_no_orientedClassPair
    {δ β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hβ : 0 < β)
    {n : ℕ} (hn : 5 ≤ n) {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hnone : ¬ OrientedClassPair vs sides n A B β (12 * (δ + 1))) :
    classLength vs n A ≤ 8 * classLength vs n Bᶜ +
      20 * (n - 4 : ℕ) * β + cutPotential n * (δ + 1) := by
  induction n using Nat.strong_induction_on generalizing vs sides A B with
  | _ n ih =>
    by_cases hn8 : n ≤ 8
    · have hs := classLength_le_of_no_orientedClassPair_small hδ hδ0 hgeo
        (show δ ≤ δ + 1 by linarith) hβ (show 2 ≤ n by omega) hn8 hpoly A B hnone
      have hb := mul_le_mul_of_nonneg_right (beta_cost_of_le_eight hn hn8) (le_of_lt hβ)
      have hc := mul_le_mul_of_nonneg_right (cutPotential_base hn hn8)
        (show 0 ≤ δ + 1 by linarith)
      linarith
    · have hn9 : 9 ≤ n := by omega
      obtain ⟨cut⟩ := exists_orientedClassifiedBisection hδ hδ0 hgeo hn9 hpoly
      have hl5 : 5 ≤ cut.m + 2 := by have := cut.low; omega
      have hr5 : 5 ≤ n - cut.m + 2 := by have := cut.high; omega
      have hln : cut.m + 2 < n := by have := cut.high; omega
      have hrn : n - cut.m + 2 < n := by have := cut.low; omega
      have hl := ih (cut.m + 2) hln hl5 cut.leftClosed
        (cut.leftClass A) (cut.leftClass B)
        (fun h => hnone (cut.leftOrientedPair A B β (12 * (δ + 1)) h))
      have hr := ih (n - cut.m + 2) hrn hr5 cut.rightClosed
        (cut.rightClass A) (cut.rightClass B)
        (fun h => hnone (cut.rightOrientedPair A B β (12 * (δ + 1)) h))
      have hfirst := cut.firstLength A
      have hshort := cut.shortLength B
      have hsumN : (cut.m + 2 - 4) + (n - cut.m + 2 - 4) = n - 4 := by
        have := cut.low
        have := cut.high
        omega
      have hsum : ((cut.m + 2 - 4 : ℕ) : ℝ) + (n - cut.m + 2 - 4 : ℕ) =
          (n - 4 : ℕ) := by exact_mod_cast hsumN
      have hpotential := cutPotential_subdivision hn9 cut.low cut.high
      have hscale := mul_le_mul_of_nonneg_right hpotential
        (show 0 ≤ δ + 1 by linarith)
      have hlog : (0 : ℝ) ≤ (Nat.clog 2 n : ℝ) + 1 := by positivity
      have hcost : 8 * (12 * δ * ((Nat.clog 2 n : ℝ) + 1) + 2) +
          (cutPotential (cut.m + 2) + cutPotential (n - cut.m + 2)) * (δ + 1) ≤
            cutPotential n * (δ + 1) := by
        nlinarith
      nlinarith

/-- The uniform linear estimate, covering polygons with two to four sides. -/
theorem classLength_le_linear_of_no_orientedClassPair
    {δ β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hβ : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hnone : ¬ OrientedClassPair vs sides n A B β (12 * (δ + 1))) :
    classLength vs n A ≤ 8 * classLength vs n Bᶜ +
      20 * (n : ℝ) * β + 40000 * n * (δ + 1) := by
  by_cases hn5 : 5 ≤ n
  · have h := classLength_le_of_no_orientedClassPair hδ hδ0 hgeo hβ hn5 hpoly A B hnone
    have hb : ((n - 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 4
    have hb' := mul_le_mul_of_nonneg_right hb (show 0 ≤ 20 * β by positivity)
    have hc := mul_le_mul_of_nonneg_right (cutPotential_le n) (show 0 ≤ δ + 1 by linarith)
    nlinarith
  · have h := classLength_le_of_no_orientedClassPair_small hδ hδ0 hgeo
      (show δ ≤ δ + 1 by linarith) hβ hn (show n ≤ 8 by omega) hpoly A B hnone
    have hb : (n : ℝ) * ((n : ℝ) - 1) ≤ 20 * n := by
      have hn4 : n ≤ 4 := by omega
      interval_cases n <;> norm_num
    have hc : 48 * (n : ℝ) * ((n : ℝ) - 1) ≤ 40000 * n := by
      have hn4 : n ≤ 4 := by omega
      interval_cases n <;> norm_num
    have hb' := mul_le_mul_of_nonneg_right hb (le_of_lt hβ)
    have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ δ + 1 by linarith)
    linarith

/-- **Ol'shanskii's three-class lemma, antiparallel form.** `A` is the first
class and `B` is the union of the first two. -/
theorem exists_orientedClassPair_of_aggregate
    {δ a : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X)
    {n : ℕ} (hn : 2 ≤ n) {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (ha : 100000 * (δ + 1) ≤ a)
    (hfirst : a * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ < a * n / 1000) :
    OrientedClassPair vs sides n A B (a / 1000) (12 * (δ + 1)) := by
  have ha0 : 0 < a := by linarith
  by_contra hnone
  have h := classLength_le_linear_of_no_orientedClassPair hδ hδ0 hgeo
    (show 0 < a / 1000 by positivity) hn hpoly A B hnone
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale := mul_le_mul_of_nonneg_right ha (le_of_lt hn0)
  have han : 0 < a * n := mul_pos ha0 hn0
  nlinarith

/-- Zero- and one-sided polygons cannot satisfy the first-class hypothesis. -/
theorem exists_orientedClassPair_of_aggregate_all
    {δ a : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X)
    {n : ℕ} {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (ha : 100000 * (δ + 1) ≤ a)
    (hfirst : a * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ < a * n / 1000) :
    OrientedClassPair vs sides n A B (a / 1000) (12 * (δ + 1)) := by
  classical
  have hn : 2 ≤ n := by
    by_contra hbad
    have hn1 : n ≤ 1 := by omega
    interval_cases n
    · simp [classLength] at hfirst
    · have hclose : vs 1 = vs 0 := by simpa using hpoly.2
      have hlen : classLength vs 1 A = 0 := by simp [classLength, hclose]
      rw [hlen] at hfirst
      norm_num at hfirst
      linarith
  exact exists_orientedClassPair_of_aggregate hδ hδ0 hgeo hn hpoly A B ha hfirst hshort

end GroupApproximation.Olshanskii

namespace GroupApproximation.Olshanskii

universe v

open GroupApproximation.HullGeometry

/-- `ThreeClassPolygonStatement` with an antiparallel pair in the conclusion. -/
def OrientedThreeClassPolygonStatement : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (X : Type v) [PseudoMetricSpace X], IsHyperbolicSpace δ X → IsGeodesicSpace X →
      ∀ (n : ℕ) (vs : ℕ → X) (sides : ℕ → ℝ → X),
        IsClosedPolygonAt vs sides 0 n →
        ∀ N₁ N₂ N₃ : Set ℕ,
          (∀ i < n, (i ∈ N₁ ∨ i ∈ N₂ ∨ i ∈ N₃) ∧
            (i ∈ N₁ → i ∉ N₂ ∧ i ∉ N₃) ∧ (i ∈ N₂ → i ∉ N₃)) →
          ∀ a : ℝ, c₂ ≤ a → a * n < classLength vs n N₁ →
            classLength vs n N₃ < a * n / 1000 →
            OrientedClassPair vs sides n N₁ (N₁ ∪ N₂) (a / 1000) c₁

/-- **Ol'shanskii's three-class lemma with antiparallel segments.** -/
theorem orientedThreeClassPolygon : OrientedThreeClassPolygonStatement.{v} := by
  intro δ hδ0
  refine ⟨12 * (δ + 1), 100000 * (δ + 1), by positivity, by positivity, ?_⟩
  intro X _ hδ hgeo n vs sides hpoly N₁ N₂ N₃ hpartition a ha hfirst hshort
  have hlength : classLength vs n (N₁ ∪ N₂)ᶜ = classLength vs n N₃ := by
    classical
    apply Finset.sum_congr rfl
    intro i hi
    have hp := hpartition i (Finset.mem_range.mp hi)
    have heq : i ∈ (N₁ ∪ N₂)ᶜ ↔ i ∈ N₃ := by
      simp only [Set.mem_compl_iff, Set.mem_union]
      tauto
    simp only [heq]
  apply exists_orientedClassPair_of_aggregate_all hδ hδ0 hgeo hpoly N₁ (N₁ ∪ N₂)
    ha hfirst
  rwa [hlength]

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.side_length_le_of_no_orientedClassPair_small
#audit_axioms GroupApproximation.Olshanskii.classLength_le_of_no_orientedClassPair_small
#audit_axioms GroupApproximation.Olshanskii.classLength_le_of_no_orientedClassPair
#audit_axioms GroupApproximation.Olshanskii.classLength_le_linear_of_no_orientedClassPair
#audit_axioms GroupApproximation.Olshanskii.exists_orientedClassPair_of_aggregate
#audit_closed_axioms GroupApproximation.Olshanskii.orientedThreeClassPolygon
