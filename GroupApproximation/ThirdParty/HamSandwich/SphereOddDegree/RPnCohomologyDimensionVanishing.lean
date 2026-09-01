import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnHomologyDimensionVanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology
import GroupApproximation.Meta.AxiomGuard
import Mathlib

/-!
# Mod-two cohomology of `RPⁿ` vanishes above the dimension

This file dualizes the mod-two homology dimension-vanishing for real projective
space to cohomology, via Kronecker duality over `F₂`:

```text
Hᵏ(RPⁿ; F₂) = 0      for n < k.
```

The homology statement `rpHomologyZMod2_isZero_above_dim` is transported to
cohomology using the universal-coefficient isomorphism `kroneckerEquiv`, exactly
as in `SphereModTwoHomologyAboveDimension.lean` for spheres.

These theorems have names distinct from the additive-branch
`rpCohomology_isZero_above`, since that route imports the good-pair/excision gap;
here the proof is direct from Kronecker duality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- **Above-dimension mod-two `RPⁿ` cohomology vanishes.** For `n < k`,
`Hᵏ(RPⁿ; F₂) = 0`. -/
theorem rpCohomology_isZero_above_dim_direct
    (n k : Nat) (hk : n < k) :
    IsZero (rpCohomology n k) := by
  have hH : IsZero (homologyZMod2 (TopCat.of (RP n)) k) :=
    rpHomologyZMod2_isZero_above_dim n k hk
  have hDual : IsZero (homologyDualZMod2 (TopCat.of (RP n)) k) :=
    homologyDualZMod2_isZero_of_homology_isZero (TopCat.of (RP n)) k hH
  exact IsZero.of_iso hDual (kroneckerEquiv (TopCat.of (RP n)) k)

/-- **Mod-two `RPⁿ` cohomology vanishes just above the top.** `H^{n+1}(RPⁿ; F₂) = 0`. -/
theorem rpCohomology_topPlusOne_isZero_direct (n : Nat) :
    IsZero (rpCohomology n (n + 1)) :=
  rpCohomology_isZero_above_dim_direct n (n + 1) (Nat.lt_succ_self n)

/-- Closed audit endpoint for RP dimension vanishing in mod-two cohomology. -/
theorem rpCohomology_dimension_vanishing_closed :
    (∀ n k : Nat, n < k → IsZero (rpCohomology n k)) ∧
    (∀ n : Nat, IsZero (rpCohomology n (n + 1))) :=
  ⟨rpCohomology_isZero_above_dim_direct,
    rpCohomology_topPlusOne_isZero_direct⟩

#audit_closed_axioms rpCohomology_dimension_vanishing_closed

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
