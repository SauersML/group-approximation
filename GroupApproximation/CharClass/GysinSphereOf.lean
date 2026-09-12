import GroupApproximation.CharClass.GysinSphere
import GroupApproximation.CharClass.KroneckerSphere
import GroupApproximation.Meta.AxiomGuard

/-!
# The unit vectors have the `K`-cohomology of the odd sphere

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`GysinSphere.lean` computes the mod-2 cohomology of the unit vectors of `ℂ^{d+1}` through the
homotopy equivalence with `S^{2d+1}`.  The equivalence is pure topology, so over a field `K`
only the sphere computation changes, and `lix-cupone`'s `KroneckerSphere` supplies it: the
top class (`sphereTopEquivOf`), degree zero (`sphereCohZeroEquivOf`) and the vanishing in
every other degree (`sphere_coh_isZero_of_neOf`).

This is a new module beside `GysinSphere` rather than an edit of it, so that the `F₂` Gysin
chain does not gain an import.

## Main declarations

* `hasSphereCohomologyOf_sphere` — the concrete sphere, over a field.
* `hasSphereCohomologyOf_unitVectors` — **the unit vectors, over a field**.
* `eq_zero_unitVectorsOf` — acyclicity below the top, the form the Gysin pair condition
  consumes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- **The concrete sphere has the `K`-cohomology of a sphere**, over any field. -/
theorem hasSphereCohomologyOf_sphere (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    HasSphereCohomologyOf K (TopCat.of (Sphere n)) n :=
  ⟨⟨sphereCohZeroEquivOf K n hn⟩, ⟨sphereTopEquivOf K n hn⟩, fun k hk hm a => by
    have h := sphere_coh_isZero_of_neOf K n k hk hm
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h.elim a 0⟩

/-- **The unit vectors have the `K`-cohomology of `S^{2d+1}`**, over any field. -/
theorem hasSphereCohomologyOf_unitVectors (K : Type) [Field K] (d : ℕ) :
    HasSphereCohomologyOf K (TopCat.of ↥(unitVectors (Fin (d + 1)))) (2 * d + 1) := by
  refine HasSphereCohomologyOf.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquivOf K (unitVectorsHomotopyEquivSphere d) k).symm) ?_
  exact hasSphereCohomologyOf_sphere K (2 * d + 1) (by omega)

/-- **The unit vectors are `K`-acyclic below the top.** -/
theorem eq_zero_unitVectorsOf (K : Type) [Field K] (d k : ℕ) (hk0 : k ≠ 0)
    (hk : k ≠ 2 * d + 1) (a : Hmod K (TopCat.of ↥(unitVectors (Fin (d + 1)))) k) : a = 0 :=
  (hasSphereCohomologyOf_unitVectors K d).2.2 k hk0 hk a

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms hasSphereCohomologyOf_unitVectors
#audit_axioms eq_zero_unitVectorsOf

end

end Gysin
end CharClass
end GroupApproximation
