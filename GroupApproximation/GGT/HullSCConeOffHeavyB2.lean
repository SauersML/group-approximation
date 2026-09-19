import GroupApproximation.GGT.HullSCConeOffHeavyEndpointBridge
import GroupApproximation.GGT.HullSCConeOffHeavyModelTransfer
import GroupApproximation.GGT.HullSCConeOffHeavyUniformThreshold

/-!
# B2, assembled: geometric separation from one geometric leaf

Six modules of this lane have taken Hull's geometric-separation clause apart.
This one puts it back together, so that what B2 still owes is visible in a single
statement rather than spread across a chain.

`isGeometricallySeparated_of_uniformThreshold` says: given

* `PairwiseNonCommensurable g` — Dahmani--Guirardel--Osin's and Hull's standing
  hypothesis on the family, and the thing the `λ = μ` half of separation is
  bought with;
* `ClosureNearPowers` at a single `ρ` — each `E(g ν)` within `ρ` of its own
  powers, which is DGO's Lemma 6.5 and is *also* the one hypothesis clause (a)
  of the cone-off leaf still carries, so it is owed once and spent twice;
* `UniformlyLoxodromic` — one set of loxodromy constants for the family, which
  `uniformlyLoxodromic_of_finite` shows is exactly what DGO's finiteness
  hypothesis in Theorem 6.8 supplies;
* `UniformCommonZpowThreshold` on the geodesic model — the geometric leaf,

the family `{E(g λ)}` is geometrically separated in `Γ(G, A)`.

## Discharge status

Of the four, the first three are hypotheses of the theorem being formalised
rather than debts: DGO and Hull assume non-commensurability and finiteness, and
`ClosureNearPowers` is their Lemma 6.5.  The former geometric leaf
`UniformCommonZpowThreshold` is now discharged by
`uniformCommonZpowThreshold_of_acylindrical`: it says nothing about Hull's
construction, and follows from hyperbolicity, geodesicity, isometry and
acylindricity after its quantitative constants are hoisted.

All three dischargeable inputs are now supplied.  For a finite family,
`uniformlyLoxodromic_of_finite` supplies the uniform constants, and
`exists_uniform_closureNearPowers_of_coarseTranslation` supplies `ρ` from
`Elementary.ElementaryClosureCoarseTranslation`, which is Lemma 6.5 itself.
`isGeometricallySeparated_of_acylindrical_of_coarseTranslation` additionally
transports the Cayley action to the geodesic model and discharges the uniform
threshold.  Its hypothesis list is the honest ledger for B2: pairwise
non-commensurability and finiteness, both assumed by the source; hyperbolicity
and acylindricity of Hull's alphabet; and Lemma 6.5 in its named form.

`GGT/HullSCConeOffHeavyUniformThreshold.lean` performs the quantifier-order
hoist.  Every constant is chosen from numeric loxodromy and displacement data,
including one larger pair-stabilizer radius supplied by acylindricity; monotonicity
then restricts it to the actual radius used by the fellow-travel proof.

## Where this feeds

Hull's Theorem 3.9 (his `crit`) takes hyperbolicity, quasi-convexity, geometric
separation and `d_X`-local finiteness and returns the full hyperbolic
embedding — clause (a) and clause (b) together, with no projection API.  This
module is its third input.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G]

/-- **Geometric separation of the elementary closures, from the geometric
leaf.**  This is Hull's third input to his Theorem 3.9, for the family
`{E(g λ)}` of a pairwise non-commensurable, uniformly loxodromic family. -/
theorem isGeometricallySeparated_of_uniformThreshold {Λ : Type w}
    (A : Alphabet G) (g : Λ → G) {rho : ℕ}
    (hncom : PairwiseNonCommensurable g)
    (hclose : ∀ nu : Λ, ClosureNearPowers A (g nu) rho)
    (hulox : UniformlyLoxodromic A g)
    (hunif : UniformCommonZpowThreshold G (CayleyGeodesicModel.PointQuot A)) :
    IsGeometricallySeparated A (fun lam => Elementary.elementaryClosure (g lam)) :=
  isGeometricallySeparated_elementaryClosure A g hncom
    (diameterForcesConjugateCommonPower_of_matchedPowers A g hclose
      (matchedPowersForceCommonPower_of_uniformThreshold A g hulox hunif))

/-- The same, for a finite family, with uniform loxodromy replaced by the
hypothesis Dahmani--Guirardel--Osin actually state: finitely many loxodromic
elements. -/
theorem isGeometricallySeparated_of_uniformThreshold_of_finite {Λ : Type w}
    [Finite Λ] [Nonempty Λ] (A : Alphabet G) (g : Λ → G) {rho : ℕ}
    (hncom : PairwiseNonCommensurable g)
    (hclose : ∀ nu : Λ, ClosureNearPowers A (g nu) rho)
    (hlox : ∀ nu : Λ, IsLoxodromic (g nu) (Cayley.base A))
    (hunif : UniformCommonZpowThreshold G (CayleyGeodesicModel.PointQuot A)) :
    IsGeometricallySeparated A (fun lam => Elementary.elementaryClosure (g lam)) :=
  isGeometricallySeparated_of_uniformThreshold A g hncom hclose
    (uniformlyLoxodromic_of_finite A g hlox) hunif

/-- **The form with every dischargeable hypothesis discharged.**

For a finite nonempty family of loxodromic elements, uniform loxodromy comes
from finiteness and the Hausdorff constant `ρ` comes from Dahmani--Guirardel--Osin's
Lemma 6.5 in its named form.  What is left is pairwise non-commensurability,
which the source assumes, Lemma 6.5, which the source proves, and the geometric
leaf — and nothing else. -/
theorem isGeometricallySeparated_of_uniformThreshold_of_coarseTranslation
    {Λ : Type w} [Fintype Λ] [Nonempty Λ] (A : Alphabet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ nu : Λ, IsLoxodromic (g nu) (Cayley.base A))
    (hct : Elementary.ElementaryClosureCoarseTranslation G (Cayley.base A))
    (hunif : UniformCommonZpowThreshold G (CayleyGeodesicModel.PointQuot A)) :
    IsGeometricallySeparated A (fun lam => Elementary.elementaryClosure (g lam)) := by
  obtain ⟨rho, hclose⟩ :=
    exists_uniform_closureNearPowers_of_coarseTranslation A g hlox hct
  exact isGeometricallySeparated_of_uniformThreshold A g hncom hclose
    (uniformlyLoxodromic_of_finite A g hlox) hunif

/-- **B2 with the uniform-threshold leaf discharged.**  Hyperbolicity and
acylindricity are transported from the Cayley graph to its geodesic metric
identification along the equivariant, additively distorted, dense vertex map;
`uniformCommonZpowThreshold_of_acylindrical` then supplies the former leaf. -/
theorem isGeometricallySeparated_of_acylindrical_of_coarseTranslation
    {Λ : Type w} [Fintype Λ] [Nonempty Λ] (A : Alphabet G) (g : Λ → G)
    {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (hacy : IsAcylindrical G (Cayley A))
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ nu : Λ, IsLoxodromic (g nu) (Cayley.base A))
    (hct : Elementary.ElementaryClosureCoarseTranslation G (Cayley.base A)) :
    IsGeometricallySeparated A (fun lam => Elementary.elementaryClosure (g lam)) := by
  have hδ0 : 0 ≤ δ :=
    Elementary.nonneg_of_isHyperbolicSpace hδ (Cayley.base A)
  have hgeoQ : IsGeodesicSpace (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isGeodesicRealisationQuot A
  have hhypQ : IsHyperbolicSpace (δ + 6) (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point A hδ)
  have hisoQ : IsIsometricAction G (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isIsometricAction_pointQuot A
  have hacyQ : IsAcylindrical G (CayleyGeodesicModel.PointQuot A) :=
    isAcylindrical_of_additiveDistortion_of_dense zero_le_one
      (CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A)
      (CayleyGeodesicModel.hasDenseImage_iotaQuot A)
      (CayleyGeodesicModel.isEquivariant_iotaQuot A) hisoQ hacy
  have hunif : UniformCommonZpowThreshold G (CayleyGeodesicModel.PointQuot A) :=
    uniformCommonZpowThreshold_of_acylindrical hhypQ (by linarith) hgeoQ hisoQ hacyQ
  exact isGeometricallySeparated_of_uniformThreshold_of_coarseTranslation
    A g hncom hlox hct hunif

end HullSC
end GroupApproximation
