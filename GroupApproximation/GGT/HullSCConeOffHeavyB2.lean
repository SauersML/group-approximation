import GroupApproximation.GGT.HullSCConeOffHeavyEndpointBridge
import GroupApproximation.GGT.HullSCConeOffHeavyModelTransfer

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

## What is a leaf and what is not

Of the four, the first three are hypotheses of the theorem being formalised
rather than debts: DGO and Hull assume non-commensurability and finiteness, and
`ClosureNearPowers` is their Lemma 6.5.  Only `UniformCommonZpowThreshold` is
owed, and it says nothing about groups acting on Cayley graphs or about Hull's
construction — a hyperbolic geodesic space, two loxodromic elements with given
constants, one basepoint, and a threshold chosen before all of them.

Two of the three are now discharged rather than assumed.  For a finite family,
`uniformlyLoxodromic_of_finite` supplies the uniform constants, and
`exists_uniform_closureNearPowers_of_coarseTranslation` supplies `ρ` from
`Elementary.ElementaryClosureCoarseTranslation`, which is Lemma 6.5 itself.
`isGeometricallySeparated_of_uniformThreshold_of_coarseTranslation` is that
form, and its hypothesis list is the honest ledger for B2: pairwise
non-commensurability and finiteness, both assumed by the source; Lemma 6.5,
carried as its named predicate; and the one geometric leaf.

`GGT/HullSCConeOffHeavyFellowTravel.lean` proves that statement with the
threshold chosen *after* the elements.  The gap between the two is quantifier
order alone, and `GGT/HullSCConeOffHeavyModelTransfer.lean` records why nothing
worse is hiding in it: every constant the threshold is built from is bounded
uniformly, by comparison with the conjugation-invariant data at a basepoint on
the element's own axis.

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

end HullSC
end GroupApproximation
