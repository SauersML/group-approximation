import GroupApproximation.GGT.DGOQuasiGeodesicChainHausdorff

/-!
# Thin quadrangles at general quasi-geodesic parameters

Morse proximity takes an original side vertex to a between-point, the
four-point quadrangle estimate crosses to another side, and reverse proximity
returns an indexed vertex on that original side. The bound is uniform in all
side lengths. A second form leaves the fourth side exempt, returning only a
between-point there, as required for a distinguished peripheral component.
-/

namespace GroupApproximation.GGT

open GroupApproximation.WordMetric

universe u
variable {G : Type u} [Group G]

/-- Uniform thinness for four `(μ,b)` chains, at their original vertices. -/
theorem exists_quadrangle_chainAt_bound (S : Set G) (mu : ℝ) (b δ : ℕ)
    (hmu : 0 < mu) :
    ∃ θ : ℕ, ∀ {a b' c e : ℕ → G} {na nb nc ne : ℕ},
      IsSymmetricGeneratingSet S → Hyperbolic.IsFourPointHyperbolic S δ →
      IsQuasiGeodesicChainAt S mu b a na → IsQuasiGeodesicChainAt S mu b b' nb →
      IsQuasiGeodesicChainAt S mu b c nc → IsQuasiGeodesicChainAt S mu b e ne →
      b' 0 = a na → c 0 = b' nb → e 0 = c nc → e ne = a 0 →
      ∀ i ≤ na,
        (∃ j : ℕ, j ≤ nb ∧ wordDist S (a i) (b' j) ≤ θ) ∨
        (∃ j : ℕ, j ≤ nc ∧ wordDist S (a i) (c j) ≤ θ) ∨
        (∃ j : ℕ, j ≤ ne ∧ wordDist S (a i) (e j) ≤ θ) := by
  obtain ⟨R, hR⟩ := exists_chainAt_hausdorff_bound S mu b δ hmu
  refine ⟨2 * R + 8 * δ, ?_⟩
  intro a b' c e na nb nc ne hS hδ ha hb hc he hab hbc hce hea i hi
  obtain ⟨p, hp, hdist⟩ := (hR a na hS hδ ha).1 i hi
  rcases exists_isBetween_of_quadrangle (x₃ := b' nb) (x₄ := c nc) hS hδ hp with
    ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · have hq' : Hyperbolic.IsBetween S (b' 0) q (b' nb) := by
      simpa only [hab] using hq
    obtain ⟨j, hj, hnear⟩ := (hR b' nb hS hδ hb).2 q hq'
    refine Or.inl ⟨j, hj, ?_⟩
    have htri := wordDist_triangle hS (a i) p q
    have htri' := wordDist_triangle hS (a i) q (b' j)
    omega
  · have hq' : Hyperbolic.IsBetween S (c 0) q (c nc) := by
      simpa only [hbc] using hq
    obtain ⟨j, hj, hnear⟩ := (hR c nc hS hδ hc).2 q hq'
    refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
    have htri := wordDist_triangle hS (a i) p q
    have htri' := wordDist_triangle hS (a i) q (c j)
    omega
  · have hq' : Hyperbolic.IsBetween S (e 0) q (e ne) := by
      simpa only [hce, hea] using hq
    obtain ⟨j, hj, hnear⟩ := (hR e ne hS hδ he).2 q hq'
    refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
    have htri := wordDist_triangle hS (a i) p q
    have htri' := wordDist_triangle hS (a i) q (e j)
    omega

/-- With one side exempt, thinness still returns indexed vertices on the
other quasi-geodesic sides and a between-point on the exempt side. -/
theorem exists_quadrangle_chainAt_exempt_bound (S : Set G) (mu : ℝ) (b δ : ℕ)
    (hmu : 0 < mu) :
    ∃ θ : ℕ, ∀ {a b' c : ℕ → G} {na nb nc : ℕ},
      IsSymmetricGeneratingSet S → Hyperbolic.IsFourPointHyperbolic S δ →
      IsQuasiGeodesicChainAt S mu b a na → IsQuasiGeodesicChainAt S mu b b' nb →
      IsQuasiGeodesicChainAt S mu b c nc → b' 0 = a na → c 0 = b' nb →
      ∀ i ≤ na,
        (∃ j : ℕ, j ≤ nb ∧ wordDist S (a i) (b' j) ≤ θ) ∨
        (∃ j : ℕ, j ≤ nc ∧ wordDist S (a i) (c j) ≤ θ) ∨
        (∃ q : G, Hyperbolic.IsBetween S (c nc) q (a 0) ∧ wordDist S (a i) q ≤ θ) := by
  obtain ⟨R, hR⟩ := exists_chainAt_hausdorff_bound S mu b δ hmu
  refine ⟨2 * R + 8 * δ, ?_⟩
  intro a b' c na nb nc hS hδ ha hb hc hab hbc i hi
  obtain ⟨p, hp, hdist⟩ := (hR a na hS hδ ha).1 i hi
  rcases exists_isBetween_of_quadrangle (x₃ := b' nb) (x₄ := c nc) hS hδ hp with
    ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · have hq' : Hyperbolic.IsBetween S (b' 0) q (b' nb) := by
      simpa only [hab] using hq
    obtain ⟨j, hj, hnear⟩ := (hR b' nb hS hδ hb).2 q hq'
    refine Or.inl ⟨j, hj, ?_⟩
    have htri := wordDist_triangle hS (a i) p q
    have htri' := wordDist_triangle hS (a i) q (b' j)
    omega
  · have hq' : Hyperbolic.IsBetween S (c 0) q (c nc) := by
      simpa only [hbc] using hq
    obtain ⟨j, hj, hnear⟩ := (hR c nc hS hδ hc).2 q hq'
    refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
    have htri := wordDist_triangle hS (a i) p q
    have htri' := wordDist_triangle hS (a i) q (c j)
    omega
  · refine Or.inr (Or.inr ⟨q, hq, ?_⟩)
    have htri := wordDist_triangle hS (a i) p q
    omega

end GroupApproximation.GGT

#audit_axioms GroupApproximation.GGT.exists_quadrangle_chainAt_bound
#audit_axioms GroupApproximation.GGT.exists_quadrangle_chainAt_exempt_bound
