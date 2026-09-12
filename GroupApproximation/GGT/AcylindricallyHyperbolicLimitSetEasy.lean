import GroupApproximation.GGT.GromovSequentialBoundary
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.GGT.PNaiveChain
import GroupApproximation.GGT.PNaiveShadow
import GroupApproximation.GGT.ElementaryIndependence
import GroupApproximation.Meta.AxiomGuard

/-!
# Two independent loxodromics give more than two limit points

The easy direction between the two spellings of non-elementarity in Osin's
definition of an acylindrically hyperbolic group: an action with two independent
loxodromic elements has a limit set with more than two points.  No acylindricity
is used.

Let `g, k` be independent loxodromic elements at `o`.

* **Convergence.**  Some power `h = gᵃ` has a local backtracking gap
  (`HullGeometry.exists_power_local_backtracking_gap`), and then
  `(hⁱ o | hʲ o)_o ≥ d(o, hⁱ o) − (C + 2δ)` for `1 ≤ i < j`
  (`PNaive.le_gromovProduct_pow_pow`).  Displacements of a loxodromic tend to
  infinity, so `(hⁱ o)` converges at infinity; so does `(h⁻ⁱ o)`, whose gap and
  displacements are those of `h`.
* **The two ends of `h` differ.**  Translating by `hʲ`, `(hⁱ o | h⁻ʲ o)_o` is the
  Gromov product at an interior point of the chain `t ↦ hᵗ o`, a quasi-geodesic,
  so it is bounded (`ElementaryMorse.gromovProduct_ends_le_of_chain`).
* **The ends of `h` differ from the positive end of `kᵇ`**, by independence.

So `h⁺`, `h⁻` and `(kᵇ)⁺` are three pairwise inequivalent limit points
(`limitSetHasMoreThanTwoPoints_of_actsNonElementarily`), and
`isAcylindricallyHyperbolicLimitSet_of_osin` is the easy direction of Osin's
Theorem 1.1 between `GGT.IsAcylindricallyHyperbolicOsin` and
`IsAcylindricallyHyperbolicLimitSet`.
-/

namespace GroupApproximation
namespace GGT
namespace SequentialBoundary

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Orbit

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- Inverse powers move the basepoint as far as powers do. -/
theorem dist_inv_pow_smul (hiso : IsIsometricAction G X) (h : G) (o : X) (n : ℕ) :
    dist o ((h⁻¹ ^ n) • o) = dist o ((h ^ n) • o) := by
  rw [inv_pow]
  exact PNaive.dist_inv_smul hiso (h ^ n) o

/-- **The positive powers of an element with a local backtracking gap converge at
infinity**, when their displacements tend to infinity. -/
theorem convergesAtInfinity_pow_of_gap {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o))
    (hesc : Filter.Tendsto (fun n : ℕ => dist o ((h ^ n) • o))
      Filter.atTop Filter.atTop) :
    ConvergesAtInfinity (fun i => (h ^ i) • o) o := by
  intro M
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hesc.eventually_ge_atTop (M + (C + 2 * δ)))
  refine ⟨max N 1, fun i j hi hj => ?_⟩
  show M ≤ gromovProduct ((h ^ i) • o) ((h ^ j) • o) o
  have hi1 : 1 ≤ i := le_trans (le_max_right _ _) hi
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hiN : N ≤ i := le_trans (le_max_left _ _) hi
  have hjN : N ≤ j := le_trans (le_max_left _ _) hj
  rcases lt_trichotomy i j with hij | hij | hji
  · have h1 := PNaive.le_gromovProduct_pow_pow hδ hδ0 hiso hloc hC hgap hi1 hij
    have h2 := hN i hiN
    linarith
  · rw [← hij, gromovProduct_self, dist_comm]
    have h2 := hN i hiN
    linarith
  · have h1 := PNaive.le_gromovProduct_pow_pow hδ hδ0 hiso hloc hC hgap hj1 hji
    have h2 := hN j hjN
    rw [gromovProduct_comm]
    linarith

/-- **The inverse powers converge at infinity too**: `h⁻¹` has the same local
backtracking and the same displacements. -/
theorem convergesAtInfinity_inv_pow_of_gap {δ C : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X) {h : G} {o : X}
    (hloc : gromovProduct (h • o) (h⁻¹ • o) o ≤ C) (hC : 0 ≤ C)
    (hgap : 2 * (C + 2 * δ) < dist o (h • o))
    (hesc : Filter.Tendsto (fun n : ℕ => dist o ((h ^ n) • o))
      Filter.atTop Filter.atTop) :
    ConvergesAtInfinity (fun i => (h⁻¹ ^ i) • o) o := by
  have hloc' : gromovProduct (h⁻¹ • o) (h⁻¹⁻¹ • o) o ≤ C := by
    rw [inv_inv, gromovProduct_comm]
    exact hloc
  have hgap' : 2 * (C + 2 * δ) < dist o (h⁻¹ • o) := by
    rw [PNaive.dist_inv_smul hiso h o]
    exact hgap
  have hfun : (fun n : ℕ => dist o ((h⁻¹ ^ n) • o)) =
      fun n : ℕ => dist o ((h ^ n) • o) :=
    funext (dist_inv_pow_smul hiso h o)
  have hesc' : Filter.Tendsto (fun n : ℕ => dist o ((h⁻¹ ^ n) • o))
      Filter.atTop Filter.atTop := by
    rw [hfun]
    exact hesc
  exact convergesAtInfinity_pow_of_gap hδ hδ0 hiso hloc' hC hgap' hesc'

/-- **A loxodromic element has a power with a local backtracking gap**, in the form
`PNaive.le_gromovProduct_pow_pow` consumes. -/
theorem exists_pow_gap_of_isLoxodromic {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {g : G} {o : X} (hg : IsLoxodromic g o) :
    ∃ a : ℕ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      gromovProduct ((g ^ a) • o) ((g ^ a)⁻¹ • o) o ≤ C ∧
        2 * (C + 2 * δ) < dist o ((g ^ a) • o) := by
  obtain ⟨a, ha, hgap⟩ :=
    exists_power_local_backtracking_gap hiso (δ := 2 * δ) (by linarith) hg
  refine ⟨a, ha, gromovProduct o ((g ^ (2 * a)) • o) ((g ^ a) • o),
    gromovProduct_nonneg _ _ _, ?_, by linarith⟩
  have hsm := gromovProduct_smul hiso (g ^ a)⁻¹ o ((g ^ (2 * a)) • o) ((g ^ a) • o)
  have e1 : (g ^ a)⁻¹ • (g ^ (2 * a)) • o = (g ^ a) • o := by
    rw [smul_smul, two_mul, pow_add, inv_mul_cancel_left]
  have e2 : (g ^ a)⁻¹ • (g ^ a) • o = o := inv_smul_smul (g ^ a) o
  rw [e1, e2] at hsm
  exact (gromovProduct_comm _ _ _).trans_le hsm.le

/-- **The two ends of a loxodromic element are distinct**: Gromov products between
its positive and negative power orbits are bounded. -/
theorem exists_bound_gromovProduct_pow_inv_pow {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    {h : G} {o : X} (hh : IsLoxodromic h o) :
    ∃ K : ℝ, ∀ i j : ℕ, gromovProduct ((h ^ i) • o) ((h⁻¹ ^ j) • o) o ≤ K := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hh
  obtain ⟨K, -, hK⟩ := ElementaryMorse.gromovProduct_ends_le_of_chain hδ hδ0
    (dist_nonneg (x := o) (y := h • o)) hl hB hgeo
  refine ⟨K, fun i j => ?_⟩
  have hedge : ∀ t, t < j + i →
      dist ((h ^ t) • o) ((h ^ (t + 1)) • o) ≤ dist o (h • o) := by
    intro t _
    have hstep := hiso (h ^ t) o (h • o)
    rw [pow_succ, ← smul_smul]
    exact hstep.le
  have hprog : ∀ s t, s ≤ t → t ≤ j + i →
      l * ((t - s : ℕ) : ℝ) - B ≤ dist ((h ^ s) • o) ((h ^ t) • o) := by
    intro s t hst _
    have e : (h ^ t) • o = (h ^ s) • (h ^ (t - s)) • o := by
      rw [smul_smul, ← pow_add, Nat.add_sub_of_le hst]
    rw [e, hiso]
    exact hlin (t - s)
  have hbound := hK (fun t => (h ^ t) • o) (j + i) hedge hprog j (Nat.le_add_right j i)
  have hbound' : gromovProduct o ((h ^ (j + i)) • o) ((h ^ j) • o) ≤ K := by
    simpa only [pow_zero, one_smul] using hbound
  have hsm := gromovProduct_smul hiso (h ^ j) ((h ^ i) • o) ((h⁻¹ ^ j) • o) o
  have e1 : (h ^ j) • (h ^ i) • o = (h ^ (j + i)) • o := by
    rw [smul_smul, ← pow_add]
  have e2 : (h ^ j) • (h⁻¹ ^ j) • o = o := by
    rw [smul_smul, inv_pow, mul_inv_cancel, one_smul]
  rw [e1, e2] at hsm
  rw [← hsm, gromovProduct_comm]
  exact hbound'

/-- **Independence bounds the Gromov products between the power orbits of powers**,
positive and negative. -/
theorem gromovProduct_pow_pow_le_of_independent {g k : G} {o : X}
    (hind : Independent g k o) :
    ∃ C : ℝ, ∀ a b i j : ℕ,
      gromovProduct (((g ^ a) ^ i) • o) (((k ^ b) ^ j) • o) o ≤ C ∧
        gromovProduct (((g ^ a)⁻¹ ^ i) • o) (((k ^ b) ^ j) • o) o ≤ C := by
  obtain ⟨C, hC⟩ := hind
  refine ⟨C, fun a b i j => ⟨?_, ?_⟩⟩
  · have h := hC ((a * i : ℕ) : ℤ) ((b * j : ℕ) : ℤ)
    simpa only [zpow_natCast, pow_mul] using h
  · have h := hC (-((a * i : ℕ) : ℤ)) ((b * j : ℕ) : ℤ)
    simpa only [zpow_neg, zpow_natCast, pow_mul, inv_pow] using h

/-- **Two independent loxodromic elements give more than two limit points.** -/
theorem limitSetHasMoreThanTwoPoints_of_actsNonElementarily {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) {S : Subgroup G} {o : X}
    (hne : ActsNonElementarily S o) :
    LimitSetHasMoreThanTwoPoints G o := by
  obtain ⟨g, -, k, -, hg, hk, hind⟩ := hne
  have hδ0 : 0 ≤ δ := by
    have hbase := hδ o o o o
    rw [min_self] at hbase
    linarith
  obtain ⟨a, ha, C₁, hC₁, hloc₁, hgap₁⟩ := exists_pow_gap_of_isLoxodromic hδ0 hiso hg
  obtain ⟨b, hb, C₂, hC₂, hloc₂, hgap₂⟩ := exists_pow_gap_of_isLoxodromic hδ0 hiso hk
  have hlox₁ : IsLoxodromic (g ^ a) o := isLoxodromic_pow hg ha
  have hlox₂ : IsLoxodromic (k ^ b) o := isLoxodromic_pow hk hb
  obtain ⟨K, hK⟩ := exists_bound_gromovProduct_pow_inv_pow hδ hδ0 hgeo hiso hlox₁
  obtain ⟨C, hC⟩ := gromovProduct_pow_pow_le_of_independent hind
  refine ⟨fun i => (g ^ a) ^ i, fun i => (g ^ a)⁻¹ ^ i, fun i => (k ^ b) ^ i,
    convergesAtInfinity_pow_of_gap hδ hδ0 hiso hloc₁ hC₁ hgap₁ hlox₁.isEscaping,
    convergesAtInfinity_inv_pow_of_gap hδ hδ0 hiso hloc₁ hC₁ hgap₁ hlox₁.isEscaping,
    convergesAtInfinity_pow_of_gap hδ hδ0 hiso hloc₂ hC₂ hgap₂ hlox₂.isEscaping,
    ?_, ?_, ?_⟩
  · exact not_equivAtInfinity_of_bounded (fun i j => hK i j)
  · exact not_equivAtInfinity_of_bounded (fun i j => (hC a b i j).2)
  · exact not_equivAtInfinity_of_bounded (fun i j => (hC a b i j).1)

end Orbit

/-- **Osin's definition, independent-loxodromics spelling, gives the limit-set
spelling**, on the same action. -/
theorem isAcylindricallyHyperbolicLimitSet_of_osin {G : Type} [Group G]
    (h : IsAcylindricallyHyperbolicOsin G) : IsAcylindricallyHyperbolicLimitSet G := by
  obtain ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy, x, hne⟩ := h
  letI := instX
  letI := instA
  exact ⟨X, instX, instA, hiso, hgeo, ⟨δ, hδ⟩, hacy,
    ⟨x, limitSetHasMoreThanTwoPoints_of_actsNonElementarily hδ hgeo hiso hne⟩⟩

/-- **An acylindrically hyperbolic group in Hull's Cayley-graph sense is
acylindrically hyperbolic in the limit-set spelling of Osin's definition.** -/
theorem isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic (G : Type)
    [Group G] [IsAcylindricallyHyperbolic G] : IsAcylindricallyHyperbolicLimitSet G :=
  isAcylindricallyHyperbolicLimitSet_of_osin (osin_of_isAcylindricallyHyperbolic G)

end SequentialBoundary
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.SequentialBoundary.dist_inv_pow_smul
#audit_axioms GroupApproximation.GGT.SequentialBoundary.convergesAtInfinity_pow_of_gap
#audit_axioms GroupApproximation.GGT.SequentialBoundary.convergesAtInfinity_inv_pow_of_gap
#audit_axioms GroupApproximation.GGT.SequentialBoundary.exists_pow_gap_of_isLoxodromic
#audit_axioms GroupApproximation.GGT.SequentialBoundary.exists_bound_gromovProduct_pow_inv_pow
#audit_axioms GroupApproximation.GGT.SequentialBoundary.gromovProduct_pow_pow_le_of_independent
#audit_axioms GroupApproximation.GGT.SequentialBoundary.limitSetHasMoreThanTwoPoints_of_actsNonElementarily
#audit_axioms GroupApproximation.GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_osin
#audit_axioms GroupApproximation.GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
