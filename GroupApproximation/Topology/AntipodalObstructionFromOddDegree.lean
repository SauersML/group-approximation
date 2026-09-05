import GroupApproximation.Topology.OddMapNormalization
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.ComplexOddMapCommonZero

/-!
# `CommonZeroProperty`, unconditionally

`GroupApproximation.TautologicalCommonZero.CommonZeroProperty` is the Chern-class
input of the STW Problem XXII counterexample (the refutation of the Trace Problem
for factorial tracially complete C*-algebras).  This file discharges it.

## The chain

1. `GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree` proves the
   odd-degree theorem for self-maps of `Sⁿ`, hence Borsuk--Ulam, hence its
   complex-coordinate form `complexOddMapCommonZero`: an odd continuous map
   `Sᵈ → (κ → ℂ)` has a zero once `2 * Nat.card κ ≤ d`.  Nothing in that tree is
   an axiom, a `sorry`, or a free hypothesis.
2. `GroupApproximation.OddMapNormalization.antipodalObstruction_of_sphereCommonZero`
   realifies `ℂ^{N+1}` as `ℝ^{2N+2}` and restricts to the unit sphere `S^{2N+1}`,
   turning that into `TautologicalAntipodal.AntipodalObstruction`.  The dimension
   count is `2 * Nat.card κ ≤ 2N < 2N + 1`, with no slack: this is the same
   sharpness recorded by `TautologicalAntipodal.not_antipodalObstruction_succ`.
3. `TautologicalAntipodal.commonZeroProperty_of_antipodalObstruction` converts
   the antipodal statement into the common-zero property of sections of `L^{⊕κ}`
   over `ℂPᴺ`.

Step 1's endpoint is the same theorem that
`GroupApproximation.STW22.complexOddMapCommonZero_unconditional`
(`GroupApproximation/Analysis/STW22UnconditionalCore.lean`) consumes on the
operator-algebraic side of the counterexample; this file is the Chern-class
vocabulary of the same input, so the two routes now rest on one theorem.

## Main declarations

* `antipodalObstruction` -- `TautologicalAntipodal.AntipodalObstruction`, proved.
* `commonZeroProperty_unconditional` --
  `TautologicalCommonZero.CommonZeroProperty`, proved.  Every consumer of
  `CommonZeroProperty` can now be fed this term.
-/

namespace GroupApproximation
namespace Topology

/-- **The Borsuk--Ulam residue of Problem XXII, proved.**  There is no
continuous, nowhere-vanishing, odd map `ℂ^{N+1} ∖ {0} → (κ → ℂ)` when
`Nat.card κ ≤ N`.

`ThirdParty.HamSandwich.SphereOddDegree.Sphere d` is by definition
`↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)`, so feeding
`complexOddMapCommonZero` to the bridge is a retyping, not a transport. -/
theorem antipodalObstruction : TautologicalAntipodal.AntipodalObstruction :=
  OddMapNormalization.antipodalObstruction_of_sphereCommonZero
    fun d κ hfin hle f hf =>
      @ThirdParty.HamSandwich.SphereOddDegree.complexOddMapCommonZero d κ hfin hle f hf

/-- **The Chern-class input of the STW Problem XXII counterexample, proved.**
Over `ℂPᴺ`, a continuous section of a direct sum of at most `N` copies of the
tautological line bundle has a zero. -/
theorem commonZeroProperty_unconditional :
    TautologicalCommonZero.CommonZeroProperty :=
  TautologicalAntipodal.commonZeroProperty_of_antipodalObstruction antipodalObstruction

end Topology
end GroupApproximation
