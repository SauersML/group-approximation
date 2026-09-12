import GroupApproximation.GGT.OsinLinealAxis
import GroupApproximation.GGT.OsinTheorem11
import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex

/-!
# A limit set with more than two points gives two independent loxodromics

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Theorem 1.1 with the
classification of §3.  For an acylindrical action, non-elementarity in the
limit-set sense forces two independent loxodromic elements.  In Osin's words,
Theorem 1.1 "rules out the parabolic and quasi-parabolic cases and characterizes
case 3) [`|Λ(G)| = 2`] in algebraic terms".

Stated at a geodesic hyperbolic space with an acylindrical isometric action, in
the vocabulary of `GGT/GromovSequentialBoundary`
(`actsNonElementarily_of_limitSetHasMoreThanTwoPoints`).  The argument:

1. A convergent orbit sequence makes the orbit unbounded, so Theorem 1.1
   (`hasLoxodromicOfUnbounded_of_geodesic`) gives a loxodromic `g`.
2. If some `f ∉ E(g)`, then `g` and `f g f⁻¹` are independent loxodromics
   (`Elementary.actsNonElementarily_of_notMem_elementaryClosure`, with the proved
   `ElementaryMorse.independentOfNoCommonZpow_of_geodesic`).
3. Otherwise `G = E(g)`, the lineal case.  Every orbit point lies within a fixed
   distance of the axis of a power `h = g^k` with a local gap
   (`Elementary.elementaryClosureOrbitClose_of_geodesic`, `exists_near_axis_pow`).
   A convergent orbit sequence eventually stays on one side of the axis, and two
   sequences on the same side are equivalent at infinity
   (`GGT/OsinLinealAxis`).  So among three convergent orbit sequences two are
   equivalent, and the limit set has at most two points.

## Manuscript status

Infrastructure for the limit-set spelling of acylindrical hyperbolicity used in
`sec:torsion-free`; certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.SequentialBoundary

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Near one axis, near the axis of a power.**  If every orbit point is within
`K` of the orbit of `g`, it is within `K` plus the displacements of
`1, g, …, g^{k−1}` of the orbit of `g^k`. -/
theorem exists_near_axis_pow (hiso : IsIsometricAction G X) {g : G} {w : X} {K : ℝ}
    (hclose : ∀ f : G, ∃ n : ℤ, dist ((g ^ n) • w) (f • w) ≤ K) {k : ℕ} (hk : 0 < k) :
    ∀ f : G, ∃ q : ℤ, dist (((g ^ k) ^ q) • w) (f • w) ≤
      K + ∑ r ∈ Finset.range k, dist w ((g ^ r) • w) := by
  intro f
  obtain ⟨n, hn⟩ := hclose f
  refine ⟨n / (k : ℤ), ?_⟩
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hsplit : g ^ n = (g ^ k) ^ (n / (k : ℤ)) * g ^ (n % (k : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add, Int.mul_ediv_add_emod]
  have hr0 : 0 ≤ n % (k : ℤ) := Int.emod_nonneg n (by omega)
  have hrk : n % (k : ℤ) < k := Int.emod_lt_of_pos n hk'
  have hrem : dist w ((g ^ (n % (k : ℤ))) • w) ≤
      ∑ r ∈ Finset.range k, dist w ((g ^ r) • w) := by
    rw [zpow_eq_pow_toNat hr0]
    exact Finset.single_le_sum (f := fun r : ℕ => dist w ((g ^ r) • w))
      (fun r _ => dist_nonneg) (Finset.mem_range.mpr (by omega))
  have hmove : dist (((g ^ k) ^ (n / (k : ℤ))) • w) ((g ^ n) • w) =
      dist w ((g ^ (n % (k : ℤ))) • w) := by
    rw [hsplit, mul_smul, hiso]
  have htri := dist_triangle (((g ^ k) ^ (n / (k : ℤ))) • w) ((g ^ n) • w) (f • w)
  linarith

/-- **Osin's Theorem 1.1, limit-set direction.**  For an acylindrical isometric
action on a geodesic hyperbolic space, a limit set with more than two points
(`LimitSetHasMoreThanTwoPoints`) gives two independent loxodromic elements. -/
theorem actsNonElementarily_of_limitSetHasMoreThanTwoPoints {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {w : X}
    (hlim : LimitSetHasMoreThanTwoPoints G w) :
    ActsNonElementarily (⊤ : Subgroup G) w := by
  classical
  have hδ0 := nonneg_delta hδ w
  obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hac⟩ := hlim
  -- the orbit is unbounded
  have hunb : ¬ ∃ B : ℝ, ∀ g ∈ (⊤ : Subgroup G), dist w (g • w) ≤ B := by
    rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ := ha (B + 1)
    have h1 := hN N N le_rfl le_rfl
    rw [gromovProduct_self, dist_comm] at h1
    have h2 := hB (a N) (Subgroup.mem_top _)
    linarith
  obtain ⟨g, -, hg⟩ := hasLoxodromicOfUnbounded_of_geodesic hδ hgeo hiso hacy w ⊤ hunb
  by_cases hall : ∀ f : G, f ∈ Elementary.elementaryClosure g
  · -- the lineal case: every convergent orbit sequence follows one end of an axis
    exfalso
    obtain ⟨K, _hK0, hclose⟩ :=
      Elementary.elementaryClosureOrbitClose_of_geodesic hδ hδ0 hgeo hiso hg
    obtain ⟨k, hk, hgapk⟩ :=
      exists_power_local_backtracking_gap hiso (δ := 2 * δ) (by linarith) hg
    have hloc : gromovProduct ((g ^ k) • w) ((g ^ k)⁻¹ • w) w ≤
        gromovProduct w ((g ^ (2 * k)) • w) ((g ^ k) • w) := by
      rw [PNaive.gromovProduct_turn_eq hiso (g ^ k) w, ← pow_mul, mul_comm]
    have hC := gromovProduct_nonneg w ((g ^ (2 * k)) • w) ((g ^ k) • w)
    have hnear := exists_near_axis_pow hiso (fun f => hclose f (hall f)) hk
    choose ma hma using fun i => hnear (a i)
    choose mb hmb using fun i => hnear (b i)
    choose mc hmc using fun i => hnear (c i)
    obtain ⟨Na, hsa⟩ := eventually_sign_of_near hδ hδ0 hiso hloc hC hgapk ha hma
    obtain ⟨Nb, hsb⟩ := eventually_sign_of_near hδ hδ0 hiso hloc hC hgapk hb hmb
    obtain ⟨Nc, hsc⟩ := eventually_sign_of_near hδ hδ0 hiso hloc hC hgapk hc hmc
    rcases hsa with hsa | hsa <;> rcases hsb with hsb | hsb <;> rcases hsc with hsc | hsc
    · exact hab (equivAtInfinity_of_near_pos hδ hδ0 hiso hloc hC hgapk ha hb hma hmb hsa hsb)
    · exact hab (equivAtInfinity_of_near_pos hδ hδ0 hiso hloc hC hgapk ha hb hma hmb hsa hsb)
    · exact hac (equivAtInfinity_of_near_pos hδ hδ0 hiso hloc hC hgapk ha hc hma hmc hsa hsc)
    · exact hbc (equivAtInfinity_of_near_neg hδ hδ0 hiso hloc hC hgapk hb hc hmb hmc hsb hsc)
    · exact hbc (equivAtInfinity_of_near_pos hδ hδ0 hiso hloc hC hgapk hb hc hmb hmc hsb hsc)
    · exact hac (equivAtInfinity_of_near_neg hδ hδ0 hiso hloc hC hgapk ha hc hma hmc hsa hsc)
    · exact hab (equivAtInfinity_of_near_neg hδ hδ0 hiso hloc hC hgapk ha hb hma hmb hsa hsb)
    · exact hab (equivAtInfinity_of_near_neg hδ hδ0 hiso hloc hC hgapk ha hb hma hmb hsa hsb)
  · -- an element outside `E(g)` conjugates `g` to an independent loxodromic
    push Not at hall
    obtain ⟨f, hf⟩ := hall
    exact Elementary.actsNonElementarily_of_notMem_elementaryClosure hiso
      (ElementaryMorse.independentOfNoCommonZpow_of_geodesic hδ hδ0 hgeo hiso hacy w)
      (Subgroup.mem_top g) (Subgroup.mem_top f) hg hf

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.exists_near_axis_pow
#audit_axioms GroupApproximation.GGT.OsinClassification.actsNonElementarily_of_limitSetHasMoreThanTwoPoints
