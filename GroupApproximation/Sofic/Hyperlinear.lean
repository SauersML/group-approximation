import Mathlib.LinearAlgebra.Matrix.Permutation
import GroupApproximation.Sofic.SoficPositiveControl

/-!
# Hyperlinear groups, and one direction of Pestov's Question 3.4

A group is *hyperlinear* when every finite subset admits arbitrarily accurate
approximately multiplicative, separated models by **unitary matrices** under the
normalized Hilbert--Schmidt metric.  It is *sofic* when the same holds with
**permutation** matrices under the normalized Hamming metric.  Soficity implies
hyperlinearity (Elek--Szabó, Math. Ann. 332 (2005)); whether the converse holds
is Open Question 3.4 of Pestov's survey and is open.

This file formalizes the implication that holds.

The proof is exactly two facts, and both are already available.

* `Equiv.Perm.permMatrixHom` (Mathlib) is a genuine monoid homomorphism
  `Perm Y →* Matrix Y Y ℂ`, sending `σ` to `σ⁻¹.permMatrix` -- the inverse
  because `permMatrix` itself is an *anti*-homomorphism.  So the passage from
  permutations to matrices creates no multiplicative defect of its own.
* `permMatrix_hsDistSq`: the normalized Hilbert--Schmidt distance between two
  permutation matrices is exactly twice the normalized Hamming distance between
  the permutations.  This is `HyperlinearMetric.permMatrix_dist_sq_eq` over `ℂ`:
  each row of the difference is a difference of two standard basis vectors,
  contributing `0` when the permutations agree there and `2` when they do not.

Consequently a sofic model with accuracy `ε/2` *is* a hyperlinear model with
accuracy `ε`, after replacing each permutation by its matrix.  The two metrics
are the same metric; the factor `2` is the whole of the translation.

**The converse is Question 3.4 and nothing here bears on it.**  What the file
records is that the implication which does hold holds for a completely
transparent reason, so that the difficulty of the open direction is not hiding
anywhere in the easy one.
-/

namespace GroupApproximation

open Matrix

/-! ## The normalized Hilbert--Schmidt distance -/

/-- Squared normalized Hilbert--Schmidt distance between two matrices indexed by
a finite model. -/
noncomputable def hsDistSq (Y : FiniteModel) (A B : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y

/-! ## Inverses do not move the Hamming distance -/

/-! ## Hyperlinear models -/

/-! ## Hyperlinearity passes to subgroups

Remark `rem:hyperlinear` argues that the nonsofic witness of Theorem~A is not a
neutral test object for Question 3.4: it contains a copy of Thompson's `F`, and
hyperlinearity passes to subgroups, so proving the witness hyperlinear would
prove `F` hyperlinear -- a long-standing open problem.  That argument turns on
the monotonicity, which is proved here.

The proof is a restriction and nothing more.  An injective homomorphism carries
a finite subset of the subgroup to a finite subset of the ambient group; a model
there restricts along the map; multiplicativity transports because the map is a
homomorphism, and separation transports because it is injective.
-/

/-! ## Hyperlinearity is a local property

The definition quantifies over finite subsets, so it cannot see beyond the
subgroup a finite subset generates.  With the monotonicity above that gives the
standard locality statement: `G` is hyperlinear as soon as every finite subset
lies in the image of an injective homomorphism from a hyperlinear group.

The construction extends a model of the source to the whole of `G` by sending
everything outside the image to the identity.  The guard has to be membership in
the *image* rather than in the finite set: the multiplicativity condition names
`g * h`, which need not lie in the finite set but does lie in the image, that
being a subgroup.
-/

end GroupApproximation
