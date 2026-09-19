import GroupApproximation.GGT.DGOQuasiGeodesicChainAt

/-!
# Both directions of Morse proximity in the vertex metric

The existing Morse theorem puts each chain vertex near a between-point.
For the reverse direction, a unit-step chain attains every integer distance
from its initial vertex up to its terminal distance. At that index, a Morse
projection and the four-point inequality bound the distance to any prescribed
between-point. This keeps the original chain and its indexed vertices.
-/

namespace GroupApproximation.GGT

open GroupApproximation.WordMetric

universe u
variable {G : Type u} [Group G]

/-- A unit-step chain attains each integer radial distance up to its endpoint. -/
theorem exists_index_wordDist_eq_of_unit_steps {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {y : ℕ → G} {n t : ℕ}
    (hstep : ∀ i, i < n → wordDist S (y i) (y (i + 1)) ≤ 1)
    (ht : t ≤ wordDist S (y 0) (y n)) :
    ∃ j : ℕ, j ≤ n ∧ wordDist S (y 0) (y j) = t := by
  have hex : ∃ j : ℕ, j ≤ n ∧ t ≤ wordDist S (y 0) (y j) := ⟨n, le_rfl, ht⟩
  let j := Nat.find hex
  have hjn : j ≤ n := (Nat.find_spec hex).1
  have htj : t ≤ wordDist S (y 0) (y j) := (Nat.find_spec hex).2
  refine ⟨j, hjn, ?_⟩
  by_cases hj0 : j = 0
  · rw [hj0] at htj ⊢
    simp only [wordDist_self] at htj ⊢
    omega
  · have hprev : ¬ (j - 1 ≤ n ∧ t ≤ wordDist S (y 0) (y (j - 1))) :=
      Nat.find_min hex (show j - 1 < j by omega)
    have hprevLt : wordDist S (y 0) (y (j - 1)) < t := by omega
    have hstep' := hstep (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at hstep'
    have htri := wordDist_triangle hS (y 0) (y (j - 1)) (y j)
    omega

/-- Proximity from the chain to between-points gives proximity in the reverse
direction, at cost `2R + 2δ`. No quasi-geodesic parameter comparison is used. -/
theorem exists_index_wordDist_le_of_isBetween_of_near {S : Set G} {δ R : ℕ}
    (hS : IsSymmetricGeneratingSet S)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ) {y : ℕ → G} {n : ℕ}
    (hstep : ∀ i, i < n → wordDist S (y i) (y (i + 1)) ≤ 1)
    (hnear : ∀ i ≤ n, ∃ p : G, Hyperbolic.IsBetween S (y 0) p (y n) ∧
      wordDist S (y i) p ≤ R) {q : G}
    (hq : Hyperbolic.IsBetween S (y 0) q (y n)) :
    ∃ j : ℕ, j ≤ n ∧ wordDist S q (y j) ≤ 2 * R + 2 * δ := by
  have hq' : wordDist S (y 0) q + wordDist S q (y n) =
      wordDist S (y 0) (y n) := hq
  obtain ⟨j, hjn, hj⟩ := exists_index_wordDist_eq_of_unit_steps hS hstep (by omega :
    wordDist S (y 0) q ≤ wordDist S (y 0) (y n))
  obtain ⟨p, hp, hdist⟩ := hnear j hjn
  refine ⟨j, hjn, ?_⟩
  have hp' : wordDist S (y 0) p + wordDist S p (y n) =
      wordDist S (y 0) (y n) := hp
  have htri0 := wordDist_triangle hS (y 0) p (y j)
  have htriN := wordDist_triangle hS (y j) p (y n)
  have hcommP := wordDist_comm hS p (y j)
  have hcommN := wordDist_comm hS (y n) (y j)
  have hcommQ := wordDist_comm hS (y n) q
  have hfour := hδ (y 0) (y n) q (y j)
  omega

/-- A uniform two-sided vertex version of Morse proximity for `(μ,b)` chains.
The radius is chosen before the chain and its length. -/
theorem exists_chainAt_hausdorff_bound (S : Set G) (mu : ℝ) (b δ : ℕ)
    (hmu : 0 < mu) :
    ∃ R : ℕ, ∀ (y : ℕ → G) (n : ℕ), IsSymmetricGeneratingSet S →
      Hyperbolic.IsFourPointHyperbolic S δ → IsQuasiGeodesicChainAt S mu b y n →
        (∀ i ≤ n, ∃ p : G, Hyperbolic.IsBetween S (y 0) p (y n) ∧
          wordDist S (y i) p ≤ R) ∧
        (∀ q : G, Hyperbolic.IsBetween S (y 0) q (y n) →
          ∃ j : ℕ, j ≤ n ∧ wordDist S q (y j) ≤ R) := by
  obtain ⟨R, hR⟩ := exists_isBetween_near_of_chainAt S mu b δ hmu
  refine ⟨2 * R + 2 * δ, ?_⟩
  intro y n hS hδ hchain
  have hnear := hR y n hS hδ hchain
  constructor
  · intro i hi
    obtain ⟨p, hp, hdist⟩ := hnear i hi
    exact ⟨p, hp, by omega⟩
  · intro q hq
    apply exists_index_wordDist_le_of_isBetween_of_near hS hδ ?_ hnear hq
    intro i hi
    have h := (hchain i (i + 1) (by omega) (by omega)).2
    simpa only [Nat.add_sub_cancel_left] using h

end GroupApproximation.GGT

#audit_axioms GroupApproximation.GGT.exists_index_wordDist_eq_of_unit_steps
#audit_axioms GroupApproximation.GGT.exists_index_wordDist_le_of_isBetween_of_near
#audit_axioms GroupApproximation.GGT.exists_chainAt_hausdorff_bound
