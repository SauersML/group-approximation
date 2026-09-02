import GroupApproximation.GGT.DGOTheorem442BoundedOrbit
import GroupApproximation.GGT.DGOTheorem442Inequality

/-!
# Proof of DGO Theorem 4.42

The bounded-orbit case is supplied by the universal-base construction.  In
the remaining case, enlarge the input hyperbolicity constant to the positive
constant `max delta 0 + 1`, form the geometric projection system, and use the
near-minimal DGO relative generating set.

Its relative Cayley graph is hyperbolic because the full-edge graph is
hyperbolic by the BBF guessing-path theorem and the two alphabets are
quasi-isometric with factor three.  DGO inequality (41) is the admissible-word
projection estimate proved in the preceding module.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open CosetGraph

/-- Increasing a four-point hyperbolicity constant preserves the four-point
condition. -/
theorem isHyperbolicSpace_mono
    {X : Type} [PseudoMetricSpace X] {delta delta' : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hle : delta ≤ delta') :
    IsHyperbolicSpace delta' X := by
  intro w x y z
  have h := hdelta w x y z
  linarith

/-- The near-minimal construction supplies the complete output of DGO
Theorem 4.42 when the ambient hyperbolicity constant is positive. -/
theorem exists_dgoTheorem442Output_of_positive
    (G : Type) [Group G] (S : Type) [PseudoMetricSpace S] [MulAction G S]
    (H : Subgroup G) (s : S) (delta : ℝ)
    (hiso : IsIsometricAction G S) (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    ∃ (D : RelGenSet G Unit) (alpha : ℝ), 0 < alpha ∧
      D.fam = (fun _ ↦ H) ∧
      (∃ delta' : ℝ, IsHyperbolicSpace delta' (Cayley D.alphabet)) ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall () n →
        alpha * dist s (h • s) ≤ (n : ℝ) := by
  let P := approxCosetEquivariantProjectionSystem
    hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  let D := nearMinimalRelGenSet hiso H s hdeltapos P.dgo442Graph
    P.dgo442Graph_adj_smul_iff P.dgo442Graph_preconnected
  obtain ⟨alpha, halpha, hlower⟩ :=
    exists_dgo442NearMinimalRelGenSet_orbitLowerBound
      hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  have hfull : ∃ delta' : ℝ, IsHyperbolicSpace delta'
      (Cayley (CosetGraph.relGenSet H P.dgo442Graph
        P.dgo442Graph_adj_smul_iff P.dgo442Graph_preconnected).alphabet) :=
    P.exists_dgo442RelGenSet_hyperbolic H
  have hnear : ∃ delta' : ℝ, IsHyperbolicSpace delta'
      (Cayley (nearMinimalRelGenSet hiso H s hdeltapos P.dgo442Graph
        P.dgo442Graph_adj_smul_iff P.dgo442Graph_preconnected).alphabet) :=
    exists_nearMinimalRelGenSet_hyperbolic_of_full hiso H s hdeltapos
      P.dgo442Graph P.dgo442Graph_adj_smul_iff
      P.dgo442Graph_preconnected hfull
  have hhyperbolic : ∃ delta' : ℝ,
      IsHyperbolicSpace delta' (Cayley D.alphabet) := by
    exact hnear
  refine ⟨D, alpha, halpha, ?_, hhyperbolic, ?_⟩
  · rfl
  · simpa only [D, dgo442NearMinimalRelGenSet, P] using hlower

/-- **Dahmani--Guirardel--Osin, Theorem 4.42**, single-subgroup case. -/
theorem dgoTheorem442_unconditional : DGOTheorem442.{0, 0} := by
  intro G _ S _ _ H s delta hiso hdelta hgeo hqc hsep
  by_cases hbounded : HasBoundedOrbitAt H s
  · exact exists_dgoTheorem442Output_of_boundedOrbit H s hbounded
  · let delta' : ℝ := max delta 0 + 1
    have hdeltale : delta ≤ delta' := by
      dsimp only [delta']
      linarith [le_max_left delta 0]
    have hdelta' : IsHyperbolicSpace delta' S :=
      isHyperbolicSpace_mono hdelta hdeltale
    have hdelta'0 : 0 ≤ delta' := by
      dsimp only [delta']
      linarith [le_max_right delta 0]
    have hdeltapos : 0 < delta' := by
      dsimp only [delta']
      linarith [le_max_right delta 0]
    exact exists_dgoTheorem442Output_of_positive G S H s delta' hiso hdelta'
      hdelta'0 hdeltapos hgeo hqc hsep

end Elementary
end GGT
end GroupApproximation
