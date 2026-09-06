import GroupApproximation.GGT.OlshanskiiClassifiedBisection
import GroupApproximation.GGT.OlshanskiiSmallClassBound

/-!
# Ol'shanskii's uniform three-class polygon lemma

This is the aggregate statement cited by Osin as Lemma 3.7 (`N123`): the
first class has total length greater than `a n`, the third less than
`a n / 1000`, and a side of the first class fellow-travels a distinct side
outside the third class for length at least `a / 1000` on both sides.

The constants `12(δ+1)` and `100000(δ+1)` are chosen before the polygon or
its number of sides. Balanced bisection, exact class accounting, and the
square-root potential supply the general case from the sampling estimate.
-/

namespace GroupApproximation.Olshanskii

open GroupApproximation.HullGeometry
open Finset

universe v
variable {X : Type v} [PseudoMetricSpace X]

private theorem beta_cost_small {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    (n : ℝ) * ((n : ℝ) - 1) ≤ 20 * (n - 4 : ℕ) := by
  interval_cases n <;> norm_num

/-- The induction keeps the target segment length fixed throughout all
cuts. Its first-class and short-class coefficients do not grow with depth. -/
theorem classLength_le_of_no_classPair
    {δ β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hβ : 0 < β)
    {n : ℕ} (hn : 5 ≤ n) {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hnone : ¬ ClassPair vs sides n A B β (12 * (δ + 1))) :
    classLength vs n A ≤ 8 * classLength vs n Bᶜ +
      20 * (n - 4 : ℕ) * β + cutPotential n * (δ + 1) := by
  induction n using Nat.strong_induction_on generalizing vs sides A B with
  | _ n ih =>
    by_cases hn8 : n ≤ 8
    · have hs := classLength_le_of_no_classPair_small hδ hδ0 hgeo
        (show δ ≤ δ + 1 by linarith) hβ (show 2 ≤ n by omega) hn8 hpoly A B hnone
      have hb := mul_le_mul_of_nonneg_right (beta_cost_small hn hn8) (le_of_lt hβ)
      have hc := mul_le_mul_of_nonneg_right (cutPotential_base hn hn8)
        (show 0 ≤ δ + 1 by linarith)
      linarith
    · have hn9 : 9 ≤ n := by omega
      obtain ⟨cut⟩ := exists_classifiedBisection hδ hδ0 hgeo hn9 hpoly
      have hl5 : 5 ≤ cut.m + 2 := by have := cut.low; omega
      have hr5 : 5 ≤ n - cut.m + 2 := by have := cut.high; omega
      have hln : cut.m + 2 < n := by have := cut.high; omega
      have hrn : n - cut.m + 2 < n := by have := cut.low; omega
      have hl := ih (cut.m + 2) hln hl5 cut.leftClosed
        (cut.leftClass A) (cut.leftClass B)
        (fun h => hnone (cut.leftPair A B β (12 * (δ + 1)) h))
      have hr := ih (n - cut.m + 2) hrn hr5 cut.rightClosed
        (cut.rightClass A) (cut.rightClass B)
        (fun h => hnone (cut.rightPair A B β (12 * (δ + 1)) h))
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

/-- A uniform linear estimate, also covering polygons with two to four
sides. It is the contrapositive of the aggregate literature statement. -/
theorem classLength_le_linear_of_no_classPair
    {δ β : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hβ : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hnone : ¬ ClassPair vs sides n A B β (12 * (δ + 1))) :
    classLength vs n A ≤ 8 * classLength vs n Bᶜ +
      20 * (n : ℝ) * β + 40000 * n * (δ + 1) := by
  by_cases hn5 : 5 ≤ n
  · have h := classLength_le_of_no_classPair hδ hδ0 hgeo hβ hn5 hpoly A B hnone
    have hb : ((n - 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 4
    have hb' := mul_le_mul_of_nonneg_right hb (show 0 ≤ 20 * β by positivity)
    have hc := mul_le_mul_of_nonneg_right (cutPotential_le n) (show 0 ≤ δ + 1 by linarith)
    nlinarith
  · have h := classLength_le_of_no_classPair_small hδ hδ0 hgeo
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

/-- **Ol'shanskii's three-class lemma (Osin Lemma 3.7).** `A` is the first
class and `B` is the union of the first two. Both constants are independent
of the side count and of the polygon. -/
theorem exists_classPair_of_aggregate
    {δ a : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X)
    {n : ℕ} (hn : 2 ≤ n) {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (ha : 100000 * (δ + 1) ≤ a)
    (hfirst : a * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ < a * n / 1000) :
    ClassPair vs sides n A B (a / 1000) (12 * (δ + 1)) := by
  have ha0 : 0 < a := by linarith
  by_contra hnone
  have h := classLength_le_linear_of_no_classPair hδ hδ0 hgeo
    (show 0 < a / 1000 by positivity) hn hpoly A B hnone
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale := mul_le_mul_of_nonneg_right ha (le_of_lt hn0)
  have han : 0 < a * n := mul_pos ha0 hn0
  nlinarith

/-- Zero- and one-sided polygons cannot satisfy the first-class hypothesis;
the uniform result therefore needs no lower bound on the number of sides. -/
theorem exists_classPair_of_aggregate_all
    {δ a : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X)
    {n : ℕ} {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (ha : 100000 * (δ + 1) ≤ a)
    (hfirst : a * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ < a * n / 1000) :
    ClassPair vs sides n A B (a / 1000) (12 * (δ + 1)) := by
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
  exact exists_classPair_of_aggregate hδ hδ0 hgeo hn hpoly A B ha hfirst hshort

end GroupApproximation.Olshanskii

namespace GroupApproximation.Olshanskii

universe v

open GroupApproximation.HullGeometry

/-- The published three-class statement, including uniform positive constants
chosen before the space and the polygon. The three sets partition the actual
side indices; their values outside that finite interval have no effect. -/
def ThreeClassPolygonStatement : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (X : Type v) [PseudoMetricSpace X], IsHyperbolicSpace δ X → IsGeodesicSpace X →
      ∀ (n : ℕ) (vs : ℕ → X) (sides : ℕ → ℝ → X),
        IsClosedPolygonAt vs sides 0 n →
        ∀ N₁ N₂ N₃ : Set ℕ,
          (∀ i < n, (i ∈ N₁ ∨ i ∈ N₂ ∨ i ∈ N₃) ∧
            (i ∈ N₁ → i ∉ N₂ ∧ i ∉ N₃) ∧ (i ∈ N₂ → i ∉ N₃)) →
          ∀ a : ℝ, c₂ ≤ a → a * n < classLength vs n N₁ →
            classLength vs n N₃ < a * n / 1000 →
            ClassPair vs sides n N₁ (N₁ ∪ N₂) (a / 1000) c₁

/-- **Ol'shanskii Lemma 25, as cited in Osin's Lemma 3.7.** -/
theorem threeClassPolygon : ThreeClassPolygonStatement.{v} := by
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
  apply exists_classPair_of_aggregate_all hδ hδ0 hgeo hpoly N₁ (N₁ ∪ N₂)
    ha hfirst
  rwa [hlength]

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.classLength_le_of_no_classPair
#audit_axioms GroupApproximation.Olshanskii.classLength_le_linear_of_no_classPair
#audit_axioms GroupApproximation.Olshanskii.exists_classPair_of_aggregate
#audit_closed_axioms GroupApproximation.Olshanskii.threeClassPolygon
