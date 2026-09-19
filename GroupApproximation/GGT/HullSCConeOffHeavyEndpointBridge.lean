import GroupApproximation.GGT.HullSCConeOffHeavyFellowTravel
import GroupApproximation.GGT.HullSCConeOffHeavyLemma67
import GroupApproximation.GGT.ElementaryCoarseTranslationCayley

/-!
# Endpoint-close power segments reduce to the common-base theorem

The diameter argument for cone-off B2 produces two power-orbit segments whose
initial endpoints are close and whose terminal endpoints are close.  The
fellow-travel theorem in `HullSCConeOffHeavyFellowTravel` is stated with a
common initial point.  This file supplies the exact bridge.

Move the second orbit from its own initial point `z'` to `z`.  Isometry keeps
the two copies of that orbit `E`-close.  Consequently its terminal point is
`2E`-close to the first terminal point, while its displacement loses at most
`2E`.  The common-base theorem can then be applied with endpoint error `2E`.

## Overlap with `GGT/HullSCConeOffHeavyModelTransfer.lean`, declared

The basepoint shift below and that module's `dist_shift_of_close_basepoint` are
the same estimate at two different levels: here between two orbits in an
abstract space, there between a vertex of the geodesic model and a point of the
translated orbit in the word metric.  Neither is derivable from the other as
stated, and the two were written independently, in two lanes, within an hour of
each other.  They are both kept because unifying them would mean choosing a
level for an argument that is genuinely used at both, but a reader who changes
one should look at the other.

The two also agree on the conclusion that matters, and reached it separately:
the threshold here is deliberately *not* claimed uniform in `t` or `i`, and
hoisting it past those parameters is exactly the remaining quantifier content of
`MatchedPowersForceCommonPower`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.GGT
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **Two long endpoint-close integer power segments share a common power.**

The threshold is uniform in the exponents and in the second starting point;
it depends only on the two acting elements, the first basepoint and the fixed
endpoint error. -/
theorem exists_common_zpow_of_endpoint_close_orbit_segments_zpow {δ E : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) (hE : 0 ≤ E)
    {a b : G} {z : X} (ha : IsLoxodromic a z) (hb : IsLoxodromic b z) :
    ∃ T : ℝ, 0 < T ∧ ∀ (z' : X) (n m : ℤ),
      dist z z' ≤ E →
      T + 2 * E ≤ dist z ((a ^ n) • z) →
      T + 2 * E ≤ dist z' ((b ^ m) • z') →
      dist ((a ^ n) • z) ((b ^ m) • z') ≤ E →
      ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ a ^ p = b ^ q := by
  obtain ⟨T, hT, hcommon⟩ :=
    exists_common_zpow_of_close_orbit_endpoints_zpow hδ hδ0 hgeo hiso hacy
      (E := 2 * E) (by linarith) ha hb
  refine ⟨T, hT, ?_⟩
  intro z' n m hstart hlongA hlongB hend
  have hmove : dist ((b ^ m) • z') ((b ^ m) • z) = dist z' z :=
    hiso (b ^ m) z' z
  have hstart' : dist z' z ≤ E := by
    rwa [dist_comm]
  have hend' : dist ((a ^ n) • z) ((b ^ m) • z) ≤ 2 * E := by
    have htri := dist_triangle ((a ^ n) • z) ((b ^ m) • z') ((b ^ m) • z)
    linarith
  have hlongB' : T ≤ dist z ((b ^ m) • z) := by
    have h1 := dist_triangle z' z ((b ^ m) • z')
    have h2 := dist_triangle z ((b ^ m) • z) ((b ^ m) • z')
    have hmove' : dist ((b ^ m) • z) ((b ^ m) • z') = dist z z' :=
      hiso (b ^ m) z z'
    linarith
  exact hcommon n m (by linarith) hlongB' hend'

/-- **The endpoint bridge in the algebraic shape produced by step 1.**

Fix the first power vertex `a ^ i`.  A segment of the `a`-orbit beginning
there and a segment of the translated `b`-orbit beginning at `t * b ^ k`
are precisely orbit segments for `a` and `t * b * t⁻¹`.  Thus close
initial and terminal power vertices force a common conjugate power once both
segments are long.

The threshold is uniform in the two terminal exponents and in the initial
exponent `k` on the translated axis.  It is deliberately *not* claimed
uniform in `t` or `i`: hoisting it past those parameters is exactly the
remaining quantifier content of `MatchedPowersForceCommonPower`. -/
theorem exists_conj_common_zpow_of_endpoint_matched_power_segments_zpow
    {δ E : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) (hE : 0 ≤ E) {a b t : G} {x : X}
    (ha : IsLoxodromic a x) (hb : IsLoxodromic b x) (i : ℤ) :
    ∃ T : ℝ, 0 < T ∧ ∀ (j k l : ℤ),
      dist ((a ^ i) • x) ((t * b ^ k) • x) ≤ E →
      T + 2 * E ≤ dist ((a ^ i) • x) ((a ^ j) • x) →
      T + 2 * E ≤ dist ((t * b ^ k) • x) ((t * b ^ l) • x) →
      dist ((a ^ j) • x) ((t * b ^ l) • x) ≤ E →
      ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧
        t * b ^ p * t⁻¹ = a ^ q := by
  let z : X := (a ^ i) • x
  have ha_z : IsLoxodromic a z :=
    isLoxodromic_of_isLoxodromic hiso ha
  have hb_conj : IsLoxodromic (t * b * t⁻¹) x :=
    isLoxodromic_conj hiso hb
  have hb_conj_z : IsLoxodromic (t * b * t⁻¹) z :=
    isLoxodromic_of_isLoxodromic hiso hb_conj
  obtain ⟨T, hT, hbridge⟩ :=
    exists_common_zpow_of_endpoint_close_orbit_segments_zpow
      hδ hδ0 hgeo hiso hacy hE ha_z hb_conj_z
  refine ⟨T, hT, ?_⟩
  intro j k l hstart hlongA hlongB hend
  have ha_terminal :
      (a ^ (j - i)) • ((a ^ i) • x) = (a ^ j) • x := by
    rw [← mul_smul, ← zpow_add, sub_add_cancel]
  have hb_element :
      (t * b * t⁻¹) ^ (l - k) * (t * b ^ k) = t * b ^ l := by
    rw [conj_zpow]
    calc
      (t * b ^ (l - k) * t⁻¹) * (t * b ^ k) =
          t * (b ^ (l - k) * b ^ k) := by group
      _ = t * b ^ l := by
        rw [← zpow_add, sub_add_cancel]
  have hb_terminal :
      ((t * b * t⁻¹) ^ (l - k)) • ((t * b ^ k) • x) =
        (t * b ^ l) • x := by
    rw [← mul_smul, hb_element]
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hbridge ((t * b ^ k) • x) (j - i) (l - k)
      hstart (by simpa only [z, ha_terminal] using hlongA)
      (by simpa only [hb_terminal] using hlongB)
      (by simpa only [z, ha_terminal, hb_terminal] using hend)
  exact ⟨q, p, hq, hp, by simpa only [conj_zpow] using hpq.symm⟩

/-! ## The finite-index Hausdorff premise and B2 assembly -/

/-- Uniform coarse translation supplies the Hausdorff premise for a finite
family.  The individual integer bounds are replaced by their finite supremum. -/
theorem exists_uniform_closureNearPowers_of_coarseTranslation
    {G : Type u} [Group G] {Λ : Type v} [Fintype Λ]
    (A : Alphabet G) (g : Λ → G)
    (hlox : ∀ nu : Λ, IsLoxodromic (g nu) (Cayley.base A))
    (hct : Elementary.ElementaryClosureCoarseTranslation G (Cayley.base A)) :
    ∃ rho : ℕ, ∀ nu : Λ, ClosureNearPowers A (g nu) rho := by
  classical
  have hall : ∀ nu : Λ, ∃ D : ℕ, ∀ b ∈ Elementary.elementaryClosure (g nu),
      ∃ b' ∈ Subgroup.zpowers (g nu), wordDist A.carrier b b' ≤ D :=
    fun nu => Elementary.exists_wordDist_zpowers_le_of_coarseTranslation
      A (hlox nu) hct
  choose D hD using hall
  refine ⟨Finset.univ.sup D, ?_⟩
  intro nu b hb
  obtain ⟨b', hb'pow, hb'dist⟩ := hD nu b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'pow
  refine ⟨k, hb'dist.trans ?_⟩
  exact Finset.le_sup (f := D) (Finset.mem_univ nu)

/-- The finite-family form used by Hull: coarse translation discharges the
Hausdorff premise, leaving only the uniform endpoint-close power theorem. -/
theorem isGeometricallySeparated_elementaryClosure_of_coarseTranslation
    {G : Type u} [Group G] {Λ : Type v} [Fintype Λ]
    (A : Alphabet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ nu : Λ, IsLoxodromic (g nu) (Cayley.base A))
    (hct : Elementary.ElementaryClosureCoarseTranslation G (Cayley.base A))
    (hendpoint : MatchedPowersForceCommonPower A g) :
    IsGeometricallySeparated A
      (fun nu => Elementary.elementaryClosure (g nu)) := by
  obtain ⟨rho, hclose⟩ :=
    exists_uniform_closureNearPowers_of_coarseTranslation A g hlox hct
  exact isGeometricallySeparated_elementaryClosure A g hncom
    (diameterForcesConjugateCommonPower_of_matchedPowers A g hclose hendpoint)

end HullSC
end GroupApproximation
