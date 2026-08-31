# Audit: uniform corner contractions in nontrivial factorial bundles

## Verdict

PASS under the explicit uniform corner hypothesis.  Locally trivial and,
more generally, countably generated isotrivial bundles with one fixed
full-fundamental-group fibre satisfy that hypothesis.  No assertion is made
for a family of nonisomorphic fibres merely because each fibre separately
has full fundamental group.  All fibres are assumed to be `II_1`; matrix
fibres are excluded because their corner unitary groups need not have the
global connectivity used by the selection theorem.

## Selection-space check

The contractions and corner isomorphisms are not selected as functions of
the base point.  They prove only uniform intrinsic local-connectivity
estimates for the weighted solution sets.  Countable Hilbert-module
stabilization puts those sets into one complete Hilbert space, while the
factor-uniform correction lemma gives lower semicontinuity across fibres.
Michael's theorem then supplies the continuous cross-fibre selection.  This
separation removes any cocycle compatibility requirement.

## Degree bookkeeping

To fill a Stiefel `S^k`, controlled Michael lifting uses corner-unitary
equi-`LC^(k-1)` and the uniform corner hypothesis in degree `k` fills the
small lifted unitary sphere.  Hence corner data through degree `d-1` give
weighted data through degree `d-1`, exactly what Michael selection over a
base of dimension `d` requires.  Jekel contractibility is used only for
global connectivity inside individual separable fibre corners, not for a
uniform local modulus.

## Limit and algebra checks

The low-band recursion is performed inside one fibre at a time.  Each
finite stage has an exact unitary trivialization and strict remaining
support slack.  There is no infinite unitary product.  Uniform weighted
tails give an operator-bounded `L^2` limit in the fibre algebra, and `L^1`
product convergence preserves source and orthogonality.  Stabilized
operator-ball recovery then turns the selected `L^2` sections into elements
of the original tracially complete algebra.

## Local triviality and cocycles

A finite trivializing cover and partition of unity make the separable
`L^2` section module countably generated.  Transition automorphisms are
trace-preserving `2`-isometries, so the corner moduli and weighted equations
are chart invariant.  The proof never tries to glue corner isomorphisms or
Jekel contractions through the cocycle.  Thus there is no cocycle
obstruction under the stated metric hypothesis.

## Firewall for genuinely varying fibres

If the fibres `N_x` vary, separate pointed contractions—even when every
`N_x` has full fundamental group—do not imply a positive common modulus.
The infimum of their local radii could be zero.  The uniform corner
condition is therefore genuine data, not a formal consequence of
pointwise contractibility or pointwise full fundamental group.  The theorem
does not claim necessity, nor does it settle bundles without that datum.
