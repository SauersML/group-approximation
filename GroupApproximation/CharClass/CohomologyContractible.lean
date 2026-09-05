import GroupApproximation.CharClass.CohomologySphere

/-!
# Mod-2 cohomology of a contractible space

`H^k(Y; F₂) = 0` for `k ≥ 1` and `H^0(Y; F₂) ≃ₗ F₂` whenever `Y` is contractible.
The point is `H_k(pt; F₂) = 0` for `k ≥ 1` (a point is totally disconnected, so
Mathlib's `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` applies),
dualized by the vendored mod-2 universal coefficient isomorphism and transported
along the homotopy equivalence `Y ≃ₕ Unit`.

This is the base case of every Mayer–Vietoris computation downstream: the
trivializing pieces of a bundle, the hemispheres of a sphere, and the affine
charts of a projective space are all contractible.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- `H^k(pt; F₂) = 0` for `k ≥ 1`. -/
theorem cohomology_unit_isZero (k : ℕ) (hk : 1 ≤ k) :
    Limits.IsZero (Hmod2 (TopCat.of Unit) k) := by
  have hUnit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat (ZMod 2)) k (ModuleCat.of (ZMod 2) (ZMod 2)) (TopCat.of Unit)
      (by omega : k ≠ 0)
  change Limits.IsZero (homologyZMod2 (TopCat.of Unit) k) at hUnit
  exact Limits.IsZero.of_iso
    (homologyDualZMod2_isZero_of_homology_isZero (TopCat.of Unit) k hUnit)
    (kroneckerEquiv (TopCat.of Unit) k)

/-- **`H^k(Y; F₂) = 0` for `k ≥ 1` and `Y` contractible.** -/
theorem cohomology_isZero_of_contractible (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y]
    (k : ℕ) (hk : 1 ≤ k) : Limits.IsZero (Hmod2 (TopCat.of Y) k) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit Y
  have h := cohomology_unit_isZero k hk
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  haveI := h
  exact (pullEquivOfHomotopyEquiv e k).toEquiv.symm.subsingleton

/-- Every class of `H^k(Y; F₂)`, `k ≥ 1`, `Y` contractible, is zero. -/
theorem cohomology_eq_zero_of_contractible (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y]
    (k : ℕ) (hk : 1 ≤ k) (a : Hmod2 (TopCat.of Y) k) : a = 0 := by
  have h := cohomology_isZero_of_contractible Y k hk
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact h.elim a 0

/-- A contractible space is nonempty. -/
theorem nonempty_of_contractible (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y] :
    Nonempty Y :=
  ⟨(ContractibleSpace.hequiv_unit Y).some.invFun ()⟩

/-- **`H^0(Y; F₂) ≃ₗ F₂` for a contractible `Y`.** -/
def cohZeroEquivOfContractible (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y] :
    Hmod2 (TopCat.of Y) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  haveI : Nonempty (TopCat.of Y) := nonempty_of_contractible Y
  haveI : PathConnectedSpace (TopCat.of Y) := inferInstanceAs (PathConnectedSpace Y)
  cohZeroEquiv (TopCat.of Y)

end

end GroupApproximation.CharClass
