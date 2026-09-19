import GroupApproximation.CharClass.ThomPuncturedRecursion
import GroupApproximation.CharClass.ThomPuncturedSphere
import GroupApproximation.CharClass.CohomologySphereZero
import GroupApproximation.CharClass.CohomologyBridge

/-!
# Spheres and contractible spaces as Künneth factors

`ThomPuncturedRecursion.KunnethFactor Y q` is the per-factor Künneth vanishing that the
punctured-product recursion consumes; fully general Künneth is not reachable here
(`cc-cohom-api`: it needs Eilenberg–Zilber, absent from Mathlib and from the vendored
tree).  This file instantiates it in the two cases the recursion meets on the sphere
side of `N = S¹ × S⁵ × ∏_j CP(d_j)`:

* a sphere factor, from `cc-cohom-api`'s green `isZero_cohomology_prod_sphere`;
* a *punctured* sphere factor, which is contractible
  (`ThomPuncturedSphere.contractibleSpace_sphere_compl`) and so needs no Künneth
  theorem at all — `cohProdContractible` already says the factor contributes nothing.

The projective side is the same two statements with `CP(d)` and `CP(d−1)` and belongs
to `cc-projective`.

## Main results

* `kunnethFactor_sphere`, `kunnethFactor_of_contractible`, `kunnethFactor_sphere_compl`.
* `puncturedAcyclic_sphere` — the sphere base case of the recursion, modulo the
  vanishing of `H^{>n}(S^n)`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **A sphere is a Künneth factor of its own dimension.** -/
theorem kunnethFactor_sphere (n : ℕ) : KunnethFactor (Sphere n) n :=
  ⟨fun A _ p hA k hk => isZero_cohomology_prod_sphere A p n hA k hk⟩

/-- **A contractible factor is a Künneth factor of dimension zero**: it contributes
nothing to the cohomology of a product, so no Künneth theorem is involved. -/
theorem kunnethFactor_of_contractible (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y] :
    KunnethFactor Y 0 :=
  kunnethFactor_of_prodEquiv Y (fun A _ n => cohProdContractible A Y n)

/-- **A punctured sphere is a Künneth factor of any dimension.**  This is the second
factor met by the recursion's `puncturedVanish` half when the right-hand factor of the
product is a sphere. -/
theorem kunnethFactor_sphere_compl {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : Metric.sphere (0 : E) 1) (q : ℕ) :
    KunnethFactor ↥({v}ᶜ : Set ↥(Metric.sphere (0 : E) 1)) q :=
  (kunnethFactor_of_contractible _).mono (Nat.zero_le q)

/-- **The sphere base case of the punctured-product recursion.**  Its puncture is
contractible by stereographic projection; the only remaining input is the vanishing of
the cohomology of the sphere above its dimension. -/
theorem puncturedAcyclic_sphere (T : CohomologyToolkit) {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (hn : 0 < n) (v : Metric.sphere (0 : E) 1)
    (hvanish : ∀ k, n < k →
      IsZero (cohomologyZMod2 (TopCat.of ↥(Metric.sphere (0 : E) 1)) k)) :
    PuncturedAcyclic ↥(Metric.sphere (0 : E) 1) n v :=
  puncturedAcyclic_of_contractible T hn hvanish (contractibleSpace_sphere_compl v)

end GroupApproximation.CharClass
