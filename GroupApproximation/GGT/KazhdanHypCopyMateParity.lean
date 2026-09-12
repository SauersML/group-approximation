import GroupApproximation.GGT.KazhdanHypGirthEightGenericProducers
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The `copyMate` seam is empty at odd exponents

`GGT/KazhdanHypGirthEightGenericProducers.lean` reduces
`ExposedPairingEulerProducer` — the third of the four open producers of
`KazhdanHypSharpExistenceAssembly.sharpExistence_of_checkedTable` — to a raw
`PlanarDiscExposedPairingGeometry`, built from `ExposedPairing.of_copyMate`.
Its closing docstring records, in prose, that this reduction cannot be
completed: `of_copyMate` glues the `n` copies of a power disc into `n / 2`
*disjoint* pairs, so at general `n` it produces `n / 2` disjoint spheres of
total Euler characteristic `n` rather than one connected sphere, and
connectedness with `χ = 2` is the whole content of
`SeamGluing.Pairing.EulerTwoCountData`.

This module adds a second, independent obstruction and states it as a theorem
rather than as a remark, so that the dead end is closed by the kernel.

## The obstruction

`PlanarDiscExposedPairingGeometry` carries a `copyMate : Equiv.Perm (Fin n)`
that is required to be involutive (`hinvol`) and to have no fixed point
(`hfree`).  A fixed-point-free involution partitions its domain into orbits of
size exactly two, so it exists only when the domain has even cardinality.
**Hence the structure is uninhabited whenever `n` is odd.**

That is not a corner case.  The torsion argument that consumes this producer
runs over every element `g` with `g ^ n = 1`, `n > 0` and `g ≠ 1` — every
possible finite order, `n = 3` included.  So no amount of work on the seam
geometry can inhabit `PlanarDiscExposedPairingGeometry` in the generality
`ExposedPairingEulerProducer` is stated in.

## What this does and does not say

It does **not** refute `ExposedPairingEulerProducer` itself.  That producer asks
for an `ExposedPairing D.diagram n`, and `ExposedPairing.of_copyMate` is only
one way to build one.  What is ruled out is the particular route through
`copyMate`, which is the only route the repository currently has.

The construction that would serve the producer is the *cyclic* gluing the
assembly's own docstring describes — copy `i` glued to copy `i + 1` around a
cycle, giving one connected sphere for every `n`.  Nothing in the repository
builds one, and a cyclic gluing is not an involution, so it is not blocked by
what is proved here.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace GGT
namespace KazhdanHypCopyMateParity

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface

/-! ## A fixed-point-free involution forces an even domain -/

/-- **An involution of `Fin n` with `n` odd has a fixed point.**

`Equiv.Perm.exists_fixed_point_of_prime` at `p = 2`: a square root of the
identity on a set whose cardinality is not divisible by `2` fixes a point. -/
theorem exists_fixedPoint_of_involutive_of_not_two_dvd {n : ℕ} (hodd : ¬ 2 ∣ n)
    (f : Equiv.Perm (Fin n)) (hinv : Function.Involutive f) : ∃ i, f i = i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ¬ (2 ∣ Fintype.card (Fin n)) := by
    simpa using hodd
  have hsq : f ^ (2 ^ 1) = 1 := by
    have h2 : f * f = 1 := Equiv.ext fun i => hinv i
    simpa [pow_two] using h2
  exact Equiv.Perm.exists_fixed_point_of_prime hcard hsq

/-- **No fixed-point-free involution of `Fin n` exists for odd `n`.**  This is
the `copyMate` field of `PlanarDiscExposedPairingGeometry`, in isolation. -/
theorem not_exists_fixedPointFree_involution_of_not_two_dvd {n : ℕ}
    (hodd : ¬ 2 ∣ n) :
    ¬ ∃ f : Equiv.Perm (Fin n), Function.Involutive f ∧ ∀ i, f i ≠ i := by
  rintro ⟨f, hinv, hfree⟩
  obtain ⟨i, hi⟩ := exists_fixedPoint_of_involutive_of_not_two_dvd hodd f hinv
  exact hfree i hi

/-! ## The seam geometry is uninhabited at odd exponents -/

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- **`PlanarDiscExposedPairingGeometry` is empty at every odd exponent.**

Its `copyMate`, `hinvol` and `hfree` fields ask for a fixed-point-free
involution of `Fin n`, which does not exist when `n` is odd.  So the reduction
`planarDiscExposedPairingEulerData_of_planarDisc` cannot be completed, and the
`copyMate` route to `ExposedPairingEulerProducer` is closed. -/
theorem isEmpty_planarDiscExposedPairingGeometry_of_not_two_dvd
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ} (hodd : ¬ 2 ∣ n)
    (D : GirthEightVKInterface.PowerDisc T g n) :
    IsEmpty (PlanarDiscExposedPairingGeometry T D) := by
  refine ⟨fun G => ?_⟩
  exact not_exists_fixedPointFree_involution_of_not_two_dvd hodd
    ⟨G.copyMate, G.hinvol, G.hfree⟩

/-- **The hypothesis of `planarDiscExposedPairingEulerData_of_planarDisc` is
unsatisfiable.**

That theorem takes a source producing a `PlanarDiscExposedPairingGeometry` for
*every* table, element, exponent and power disc.  Instantiating it at any odd
exponent for which a power disc exists contradicts the previous theorem.  So the
route it opens is closed as soon as one odd-exponent power disc is exhibited,
and the torsion argument needs exactly those. -/
theorem not_planarDiscExposedPairingGeometry_source
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {g : TriangularHodgeLayer.Presented T} {n : ℕ} (hodd : ¬ 2 ∣ n)
    (D : GirthEightVKInterface.PowerDisc T g n) :
    ¬ Nonempty (PlanarDiscExposedPairingGeometry T D) := by
  rw [not_nonempty_iff]
  exact isEmpty_planarDiscExposedPairingGeometry_of_not_two_dvd T hodd D

end KazhdanHypCopyMateParity
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypCopyMateParity.exists_fixedPoint_of_involutive_of_not_two_dvd

#audit_axioms GroupApproximation.GGT.KazhdanHypCopyMateParity.not_exists_fixedPointFree_involution_of_not_two_dvd

#audit_axioms GroupApproximation.GGT.KazhdanHypCopyMateParity.isEmpty_planarDiscExposedPairingGeometry_of_not_two_dvd

#audit_axioms GroupApproximation.GGT.KazhdanHypCopyMateParity.not_planarDiscExposedPairingGeometry_source
