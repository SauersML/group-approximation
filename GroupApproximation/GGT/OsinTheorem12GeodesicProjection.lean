import GroupApproximation.GGT.OsinTheorem12OneDebt
import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex
import GroupApproximation.GGT.ElementaryFiniteTransversalConsequences
import GroupApproximation.GGT.ElementaryGeometricSeparationReduction

/-!
# The geodesic DGO 6.8 reduction with Lemma 6.5 discharged

For a geodesic hyperbolic action, the finite-index conclusion of DGO Lemma 6.5
is a theorem of this development: the elementary-closure orbit is uniformly
close to the power orbit, and eventual WPD turns that bound into a finite
cyclic transversal.  Consequently it is not an input to geodesic DGO 6.8.

The two remaining source boundaries are exactly the projection theorem DGO
4.42 and the long-overlap core of DGO Lemma 6.7.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

/-- The power-orbit core of DGO Lemma 6.7.  This is the form consumed by the
quasi-axis/WPD argument: a long overlap between the power orbit of `h` and its
`g`-translate forces `g` to conjugate a nonzero power of `h` to another. -/
def PowerOrbitDiameterForcesConjugatePowerAt {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X] (h : G) (x : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ g : G,
    (∀ D : ℝ, D < R → ∃ i j k l : ℤ,
      D ≤ dist ((h ^ i) • x) ((h ^ j) • x) ∧
      dist ((h ^ i) • x) ((g * h ^ k) • x) ≤ ε ∧
      dist ((h ^ j) • x) ((g * h ^ l) • x) ≤ ε) →
    ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ g * h ^ p * g⁻¹ = h ^ q

/-- DGO Lemma 6.7 at every geodesic `(AH₃)` witness, stated only for power
orbits.  Uniform closeness of `E(h) • x` to `⟨h⟩ • x` is proved below and
promotes this to the published elementary-orbit conclusion. -/
def DGOTheorem68PowerOverlap : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, v} G),
    @PowerOrbitDiameterForcesConjugatePowerAt G _ D.Space D.metricSpace D.mulAction
      D.elt D.base

/-- Uniform closeness of the elementary-closure orbit to the power orbit
promotes the power-orbit form of DGO Lemma 6.7 to the exact geometric-separation
input.  The overlap radius increases by `2K`, and its diameter decreases by at
most `2K`. -/
theorem diameterForcesConjugatePowerAt_of_powerOrbit
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hclose : ElementaryClosureOrbitClose h x)
    (hpower : PowerOrbitDiameterForcesConjugatePowerAt h x) :
    DiameterForcesConjugatePowerAt h x := by
  obtain ⟨K, hK, hclose⟩ := hclose
  intro ε hε
  have hε' : 0 < ε + (K + K) := by linarith
  obtain ⟨R, hR, hforce⟩ := hpower (ε + (K + K)) hε'
  refine ⟨R + (K + K) + 1, by linarith, ?_⟩
  intro g hoverlap
  apply hforce g
  intro D hDR
  obtain ⟨a, b, ha, hb, hab, ⟨c, hc, hac⟩, ⟨d, hd, hbd⟩⟩ :=
    hoverlap (D + (K + K)) (by linarith)
  obtain ⟨i, hai⟩ := hclose a ha
  obtain ⟨j, hbj⟩ := hclose b hb
  obtain ⟨k, hck⟩ := hclose c hc
  obtain ⟨l, hdl⟩ := hclose d hd
  refine ⟨i, j, k, l, ?_, ?_, ?_⟩
  · have htri := dist_triangle4 (a • x) ((h ^ i) • x) ((h ^ j) • x) (b • x)
    rw [dist_comm (a • x) ((h ^ i) • x)] at htri
    linarith
  · have hg : dist ((g * c) • x) ((g * h ^ k) • x) =
        dist (c • x) ((h ^ k) • x) := by
      simpa only [mul_smul] using hiso g (c • x) ((h ^ k) • x)
    calc
      dist ((h ^ i) • x) ((g * h ^ k) • x) ≤
          dist ((h ^ i) • x) (a • x) + dist (a • x) ((g * c) • x) +
            dist ((g * c) • x) ((g * h ^ k) • x) := dist_triangle4 _ _ _ _
      _ ≤ K + ε + K := by rw [hg, dist_comm (c • x) ((h ^ k) • x)]; linarith
      _ = ε + (K + K) := by ring
  · have hg : dist ((g * d) • x) ((g * h ^ l) • x) =
        dist (d • x) ((h ^ l) • x) := by
      simpa only [mul_smul] using hiso g (d • x) ((h ^ l) • x)
    calc
      dist ((h ^ j) • x) ((g * h ^ l) • x) ≤
          dist ((h ^ j) • x) (b • x) + dist (b • x) ((g * d) • x) +
            dist ((g * d) • x) ((g * h ^ l) • x) := dist_triangle4 _ _ _ _
      _ ≤ K + ε + K := by rw [hg, dist_comm (d • x) ((h ^ l) • x)]; linarith
      _ = ε + (K + K) := by ring

/-- **DGO 6.8 for geodesic witnesses from two source inputs.**

The formerly separate finite-transversal input is derived from loxodromy, WPD,
hyperbolicity and geodesicity.  It supplies quasiconvexity, properness, and
properness of `E(h)` in a non-virtually-cyclic ambient group.  Lemma 6.7 supplies
geometric separation, after which DGO 4.42 produces the hyperbolic embedding. -/
theorem dgoTheorem68_of_geodesic_projection
    (h442 : DGOTheorem442.{u, v})
    (hpower : DGOTheorem68PowerOverlap.{u, v}) :
    DGOTheorem68.{u, v} := by
  intro G _inst D hnvc
  letI : PseudoMetricSpace D.Space := D.metricSpace
  letI : MulAction G D.Space := D.mulAction
  have hδ0 : 0 ≤ D.delta := nonneg_of_isHyperbolicSpace D.hyperbolic D.base
  have hclose : ElementaryClosureOrbitClose D.elt D.base :=
    elementaryClosureOrbitClose_of_geodesic D.hyperbolic hδ0 D.geodesic
      D.isometric D.loxodromic
  have heventual : IsWPDAtEventually D.elt D.base :=
    isWPDAtEventually_of_geodesic D.hyperbolic hδ0 D.geodesic D.isometric
      D.loxodromic D.wpd
  have hfin : ElementaryClosureFiniteTransversal D.elt :=
    exists_finite_transversal_elementaryClosure_of_orbitClose D.isometric
      D.loxodromic heventual hclose
  have hqc : IsQuasiconvexOrbitAt (elementaryClosure D.elt) D.base :=
    isQuasiconvexOrbitAt_elementaryClosure_of_finiteTransversal D.hyperbolic
      hδ0 D.isometric D.loxodromic hfin
  have hproper : ActsProperlyAt (elementaryClosure D.elt) D.base :=
    actsProperlyAt_elementaryClosure_of_finiteTransversal D.isometric
      D.loxodromic hfin
  have hsep : GeometricallySeparatedAt (elementaryClosure D.elt) D.base :=
    geometricallySeparatedAt_elementaryClosure_of_diameterForcesConjugatePower
        (diameterForcesConjugatePowerAt_of_powerOrbit D.isometric hclose
        (hpower G D))
  have hemb : IsHypEmbedded G (elementaryClosure D.elt) :=
    isHypEmbedded_of_dgo442 h442 (elementaryClosure D.elt) D.base D.delta
      D.isometric D.hyperbolic D.geodesic hqc hsep hproper
  have hne : elementaryClosure D.elt ≠ ⊤ :=
    elementaryClosure_ne_top_of_finiteTransversal hfin hnvc
  exact ⟨elementaryClosure D.elt, self_mem_elementaryClosure D.elt, hne, hemb⟩

/-- Osin's `(AH₃) ⇒ (AH₁)` implication after geodesic replacement, with
the finite-index part of DGO 6.8 no longer exposed as an assumption. -/
theorem osinTheorem12_of_geodesic_projection
    (h442 : DGOTheorem442.{u, v})
    (hpower : DGOTheorem68PowerOverlap.{u, v}) :
    OsinTheorem12.{u, v} :=
  osinTheorem12_of_dgoTheorem68
    (dgoTheorem68_of_geodesic_projection h442 hpower)

end Elementary
end GGT
end GroupApproximation
