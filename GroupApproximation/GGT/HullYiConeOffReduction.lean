import GroupApproximation.GGT.HullYiStatements
import GroupApproximation.GGT.HullSCConeOffHeavyUnconditional
import GroupApproximation.GGT.HullSCConeOffHeavyEndpointBridge

/-!
# The Yi-to-cone-off geometric boundary

For the elementary closures produced by Hull's `yi`, the existing heavy lane
now supplies both geometric inputs to the prescribed-base hyperbolic embedding:

* uniform coarse translation makes the cone-off hyperbolic (clause (a));
* the endpoint-close common-power theorem makes the family geometrically
  separated (B2).

The theorem below assembles those results and leaves exactly clause (b), local
finiteness of the relative balls for this same prescribed cone-off.  It does
not replace that premise by an existential-base version of DGO Theorem 4.42:
Hull's consumer needs the original alphabet `A`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **The complete currently-formalized geometry of Hull's elementary-closure
pair.**

The first conclusion is the full prescribed-base hyperbolic embedding, with
its sole unproved input exposed as `hloc`.  The second records B2 explicitly,
so the endpoint-close work is consumed rather than hidden behind that remaining
local-finiteness premise. -/
theorem elementaryClosurePair_geometry_of_inputs
    {G : Type u} [Group G] (A : HullGeneratingSet G) (g : Bool → G)
    (hlox : ∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet))
    (hncom : ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
      c⁻¹ * g false ^ p * c ≠ g true ^ q)
    (hct : Elementary.ElementaryClosureCoarseTranslation G
      (Cayley.base A.alphabet))
    (hendpoint : MatchedPowersForceCommonPower A.alphabet g)
    (hloc : ∀ (b : Bool) (n : ℕ),
      ((coneOffFamily A.alphabet
        (fun c => Elementary.elementaryClosure (g c))).relBall b n).Finite) :
    (coneOffFamily A.alphabet
      (fun b => Elementary.elementaryClosure (g b))).IsHyperbolicallyEmbedded ∧
    IsGeometricallySeparated A.alphabet
      (fun b => Elementary.elementaryClosure (g b)) := by
  obtain ⟨rho, hnear⟩ :=
    exists_uniform_closureNearPowers_of_coarseTranslation
      A.alphabet g hlox hct
  have hclose : ∀ b : Bool, ∀ x ∈ Elementary.elementaryClosure (g b),
      ∃ y ∈ Subgroup.zpowers (g b),
        wordDist A.alphabet.carrier x y ≤ rho := by
    intro b x hx
    obtain ⟨k, hk⟩ := hnear b x hx
    exact ⟨g b ^ k,
      Subgroup.zpow_mem _ (Subgroup.mem_zpowers (g b)) k, hk⟩
  have hhyp := exists_hyperbolic_coneOffFamily_of_close A g hlox
    (fun b => Elementary.elementaryClosure (g b))
    (fun b => Elementary.zpowers_le_elementaryClosure (g b)) rho hclose
  have hsep : IsGeometricallySeparated A.alphabet
      (fun b => Elementary.elementaryClosure (g b)) :=
    isGeometricallySeparated_elementaryClosure_of_coarseTranslation
      A.alphabet g (pairwiseNonCommensurable_bool_of_notCommensurable hncom)
        hlox hct hendpoint
  exact ⟨⟨hhyp, hloc⟩, hsep⟩

end HullSC
end GroupApproximation
