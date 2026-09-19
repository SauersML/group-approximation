import GroupApproximation.GGT.DGOTheorem442NearMinimalProjection
import GroupApproximation.GGT.DGOTheorem442RelativeGeneratingSet

/-!
# Uniform one-letter projection estimates for DGO Theorem 4.42

This file proves estimate (46) from DGO section 4.5 in the single-subgroup
setting.  A near-minimal base letter has uniformly bounded projection span on
every coset orbit.  For a peripheral letter, the same conclusion holds away
from the identity orbit.

There are three cases for a base letter.  The two endpoint orbits use the
near-minimal endpoint estimate.  Every other orbit uses projection-graph
adjacency and the `2 * xi` comparison between the original and perturbed BBF
projection distances.  Peripheral letters use the uniform diameter bound of
DGO Lemma 4.46.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open CosetGraph

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- Every approximate projection of `a` and every approximate projection of
`b` to the coset orbit `Y` are at distance at most `C`. -/
def ApproxProjectionSpanLE
    (H : Subgroup G) (s : S) (delta : ℝ) (Y : G ⧸ H)
    (a b : S) (C : ℝ) : Prop :=
  ∀ p : S, IsApproxProjectionTo (cosetOrbitAt H s Y) a p delta →
    ∀ q : S, IsApproxProjectionTo (cosetOrbitAt H s Y) b q delta →
      dist p q ≤ C

/-- On a one-point metric model the projection-span predicate holds for every
target and every nonnegative bound. -/
theorem approxProjectionSpanLE_trivialModel
    [Subsingleton S] (H : Subgroup G) (s : S) (delta : ℝ)
    (Y : G ⧸ H) {C : ℝ} (hC : 0 ≤ C) :
    ApproxProjectionSpanLE H s delta Y s s C := by
  intro p _hp q _hq
  have hpq : p = q := Subsingleton.elim p q
  rw [hpq, dist_self]
  exact hC

omit [PseudoMetricSpace S] in
/-- The basepoint belongs to the identity coset orbit. -/
theorem self_mem_identityCosetOrbit (H : Subgroup G) (s : S) :
    s ∈ cosetOrbitAt H s (QuotientGroup.mk 1) := by
  rw [cosetOrbitAt_mk]
  exact ⟨1, H.one_mem, by simp⟩

omit [PseudoMetricSpace S] in
/-- `g s` belongs to the orbit indexed by `gH`. -/
theorem smul_mem_cosetOrbit_mk (H : Subgroup G) (s : S) (g : G) :
    g • s ∈ cosetOrbitAt H s (QuotientGroup.mk g) := by
  rw [cosetOrbitAt_mk]
  exact ⟨1, H.one_mem, by simp⟩

/-- The basepoint is an exact, so also a nonnegative-error, projection of
itself to the subgroup orbit. -/
theorem isApproxProjectionTo_subgroupOrbit_self
    (H : Subgroup G) (s : S) {delta : ℝ} (hdelta0 : 0 ≤ delta) :
    IsApproxProjectionTo (subgroupOrbitAt H s) s s delta := by
  refine ⟨⟨1, H.one_mem, by simp⟩, ?_⟩
  intro z _hz
  simp only [dist_self]
  linarith [dist_nonneg (x := s) (y := z)]

/-- The projection-distance field of the geometric projection system is the
diameter defined from approximate coset projections. -/
@[simp] theorem approxCosetEquivariantProjectionSystem_projDist
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) (Y A B : G ⧸ H) :
    (approxCosetEquivariantProjectionSystem
      hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep).toProjectionSystem.projDist
        Y A B = approxCosetProjectionDistance H s delta Y A B := by
  rfl

/-- The identity-endpoint projection span of a near-minimal representative is
at most `29 * delta + 4 * sigma`. -/
theorem identity_endpoint_span_le
    {delta sigma : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ sigma)
    (hsigma0 : 0 ≤ sigma) {g : G}
    (hnear : IsDoubleCosetNearMinimal H s delta g) :
    ApproxProjectionSpanLE H s delta (QuotientGroup.mk 1)
      s (g • s) (29 * delta + 4 * sigma) := by
  intro p hp q hq
  have hp' : IsApproxOrbitProjectionAt H s s p delta := by
    change IsApproxProjectionTo (subgroupOrbitAt H s) s p delta
    simpa only [cosetOrbitAt_mk, leftCosetOrbitAt_one] using hp
  have hq' : IsApproxOrbitProjectionAt H s (g • s) q delta := by
    change IsApproxProjectionTo (subgroupOrbitAt H s) (g • s) q delta
    simpa only [cosetOrbitAt_mk, leftCosetOrbitAt_one] using hq
  have hsproj := isApproxProjectionTo_subgroupOrbit_self H s hdelta0
  have hps : dist p s ≤ 14 * delta + 2 * sigma :=
    dist_approxOrbitProjection_le hdelta hdelta0 hgeo hquasi hp' hsproj
  have hsq : dist s q ≤ 2 * sigma + 15 * delta :=
    dist_approxProjection_nearMinimal_le hdelta hdelta0 hdeltapos hgeo hiso
      hquasi hsigma0 hnear hq'
  have htri := dist_triangle p s q
  linarith

/-- The other endpoint orbit satisfies the same span estimate, by translating
with the inverse representative. -/
theorem other_endpoint_span_le
    {delta sigma : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ sigma)
    (hsigma0 : 0 ≤ sigma) {g : G}
    (hnear : IsDoubleCosetNearMinimal H s delta g) :
    ApproxProjectionSpanLE H s delta (QuotientGroup.mk g)
      s (g • s) (29 * delta + 4 * sigma) := by
  intro p hp q hq
  have hpTranslated := isApproxProjectionTo_smul hiso g⁻¹
    (cosetOrbitAt H s (QuotientGroup.mk g)) hp
  have hqTranslated := isApproxProjectionTo_smul hiso g⁻¹
    (cosetOrbitAt H s (QuotientGroup.mk g)) hq
  have horbit := cosetOrbitAt_smul H s g⁻¹ (QuotientGroup.mk g)
  have hp' : IsApproxProjectionTo (subgroupOrbitAt H s)
      (g⁻¹ • s) (g⁻¹ • p) delta := by
    rw [← horbit] at hpTranslated
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel,
      cosetOrbitAt_mk, leftCosetOrbitAt_one] using hpTranslated
  have hq' : IsApproxProjectionTo (subgroupOrbitAt H s)
      s (g⁻¹ • q) delta := by
    rw [← horbit] at hqTranslated
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel,
      cosetOrbitAt_mk, leftCosetOrbitAt_one, inv_smul_smul] using hqTranslated
  have hnearInv := isDoubleCosetNearMinimal_inv hiso H s hnear
  have hsp : dist s (g⁻¹ • p) ≤ 2 * sigma + 15 * delta :=
    dist_approxProjection_nearMinimal_le hdelta hdelta0 hdeltapos hgeo hiso
      hquasi hsigma0 hnearInv hp'
  have hsproj := isApproxProjectionTo_subgroupOrbit_self H s hdelta0
  have hsq : dist s (g⁻¹ • q) ≤ 14 * delta + 2 * sigma :=
    dist_approxOrbitProjection_le hdelta hdelta0 hgeo hquasi hsproj hq'
  have htri := dist_triangle (g⁻¹ • p) s (g⁻¹ • q)
  have hpq : dist p q = dist (g⁻¹ • p) (g⁻¹ • q) :=
    (hiso g⁻¹ p q).symm
  rw [dist_comm s (g⁻¹ • p)] at hsp
  rw [hpq]
  linarith

/-- A base letter has uniformly bounded projection span on every coset orbit.
This is the base-letter half of DGO estimate (46). -/
theorem nearMinimalBase_projectionSpan_le
    {delta sigma : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ sigma)
    (hsigma0 : 0 ≤ sigma) (hsep : GeometricallySeparatedAt H s)
    (hqc : IsQuasiconvexOrbitAt H s) :
    let P := approxCosetEquivariantProjectionSystem
      hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
    ∀ {g : G}, g ∈ nearMinimalBase H s delta P.dgo442Graph →
      ∀ Y : G ⧸ H, ApproxProjectionSpanLE H s delta Y s (g • s)
        (max (29 * delta + 4 * sigma) (P.dgo442Threshold + 2 * P.ξ)) := by
  dsimp only
  let P := approxCosetEquivariantProjectionSystem
    hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  intro g hg Y
  let A : G ⧸ H := QuotientGroup.mk 1
  let B : G ⧸ H := QuotientGroup.mk g
  by_cases hYA : Y = A
  · subst Y
    exact fun p hp q hq ↦
      (identity_endpoint_span_le hdelta hdelta0 hdeltapos hgeo hiso
        hquasi hsigma0 hg.2 p hp q hq).trans (le_max_left _ _)
  by_cases hYB : Y = B
  · subst Y
    exact fun p hp q hq ↦
      (other_endpoint_span_le hdelta hdelta0 hdeltapos hgeo hiso
        hquasi hsigma0 hg.2 p hp q hq).trans (le_max_left _ _)
  intro p hp q hq
  have hgAdj : P.dgo442Graph.Adj A B := hg.1
  have hAB : A ≠ B := hgAdj.1
  have hpSet : p ∈ approxCosetProjectionSet H s delta Y A :=
    ⟨s, self_mem_identityCosetOrbit H s, hp⟩
  have hqSet : q ∈ approxCosetProjectionSet H s delta Y B :=
    ⟨g • s, smul_mem_cosetOrbit_mk H s g, hq⟩
  have hbounded := approxCosetProjectionPairSet_isBounded
    hdelta hdelta0 hdeltapos hgeo hiso hqc hsep Y A B hYA hYB
  have hpq : dist p q ≤ approxCosetProjectionDistance H s delta Y A B := by
    exact Metric.dist_le_diam_of_mem hbounded (Or.inl hpSet) (Or.inr hqSet)
  have hgraph : P.toProjectionSystem.bbfProjDist Y A B ≤
      P.dgo442Threshold := hgAdj.2 Y hYA hYB
  have hclose := P.toProjectionSystem.projDist_sub_bbfProjDist_le_two_mul
    hYA hYB hAB
  have horiginal : P.toProjectionSystem.projDist Y A B ≤
      P.dgo442Threshold + 2 * P.ξ := by
    linarith
  rw [approxCosetEquivariantProjectionSystem_projDist] at horiginal
  have hpq' : dist p q ≤ P.dgo442Threshold + 2 * P.ξ := by
    exact hpq.trans horiginal
  exact hpq'.trans (le_max_right _ _)

/-- A peripheral letter has bounded projection span away from the identity
orbit.  This is the peripheral-letter half of DGO estimate (46). -/
theorem peripheral_projectionSpan_le
    {delta nu : ℝ} {H : Subgroup G} {s : S}
    (hnu : ∀ (Y Z : G ⧸ H), Y ≠ Z →
      ∀ x ∈ approxCosetProjectionSet H s delta Y Z,
        ∀ y ∈ approxCosetProjectionSet H s delta Y Z, dist x y ≤ nu)
    {g : G} (hg : g ∈ H) {Y : G ⧸ H}
    (hY : Y ≠ QuotientGroup.mk 1) :
    ApproxProjectionSpanLE H s delta Y s (g • s) nu := by
  intro p hp q hq
  have hpSet : p ∈ approxCosetProjectionSet H s delta Y (QuotientGroup.mk 1) :=
    ⟨s, self_mem_identityCosetOrbit H s, hp⟩
  have hgOrbit : g • s ∈ cosetOrbitAt H s (QuotientGroup.mk 1) := by
    rw [cosetOrbitAt_mk, leftCosetOrbitAt_one]
    exact ⟨g, hg, rfl⟩
  have hqSet : q ∈ approxCosetProjectionSet H s delta Y (QuotientGroup.mk 1) :=
    ⟨g • s, hgOrbit, hq⟩
  exact hnu Y (QuotientGroup.mk 1) hY p hpSet q hqSet

/-- There is one positive constant for all one-letter projection estimates in
DGO section 4.5. -/
theorem exists_dgo442_letter_projection_bound
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    let P := approxCosetEquivariantProjectionSystem
      hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
    ∃ C : ℝ, 0 < C ∧
      (∀ g ∈ nearMinimalBase H s delta P.dgo442Graph, ∀ Y : G ⧸ H,
        ApproxProjectionSpanLE H s delta Y s (g • s) C) ∧
      (∀ g ∈ H, ∀ Y : G ⧸ H, Y ≠ QuotientGroup.mk 1 →
        ApproxProjectionSpanLE H s delta Y s (g • s) C) := by
  dsimp only
  let P := approxCosetEquivariantProjectionSystem
    hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  let sigma : ℝ := Classical.choose hqc
  have hqcspec := Classical.choose_spec hqc
  have hsigma0 : 0 ≤ sigma := hqcspec.1
  have hquasi := hqcspec.2
  obtain ⟨nu, _hnu0, hnu⟩ :=
    exists_approxCosetProjectionSet_diameter_bound
      hdelta hdelta0 hgeo hiso hqc hsep
  let C₀ : ℝ := max (29 * delta + 4 * sigma)
    (P.dgo442Threshold + 2 * P.ξ)
  let C : ℝ := max C₀ nu + 1
  have hC0 : 0 < C := by
    have hbase0 : 0 ≤ 29 * delta + 4 * sigma := by positivity
    have hC₀0 : 0 ≤ C₀ := le_trans hbase0 (le_max_left _ _)
    dsimp only [C]
    linarith [le_max_left C₀ nu]
  refine ⟨C, hC0, ?_, ?_⟩
  · intro g hg Y
    have hspan := nearMinimalBase_projectionSpan_le hdelta hdelta0 hdeltapos
      hgeo hiso hquasi hsigma0 hsep hqc hg Y
    intro p hp q hq
    have hpq := hspan p hp q hq
    dsimp only [C, C₀]
    exact hpq.trans (by linarith [le_max_left C₀ nu])
  · intro g hg Y hY
    have hspan := peripheral_projectionSpan_le hnu hg hY
    intro p hp q hq
    have hpq := hspan p hp q hq
    dsimp only [C]
    exact hpq.trans (by linarith [le_max_right C₀ nu])

end Elementary
end GGT
end GroupApproximation
