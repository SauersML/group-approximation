---
rg: 2
id: irreducible-dimension-lock-refutes-strict-iwahori-tubes
kind: route
title: Balance compressed Steinberg torsion spectra and force two irreducibles into one insufficient dimension
target: strict-iwahori-repair-has-no-uniform-hs-neighborhood
requires:
  - sl2-s-arithmetic-pair-is-codense-kazhdan
artifacts:
  - research/artifacts/strict-iwahori-stratum-neighborhood-obstruction-2026-09-08.md
---

Use the prerequisite with `p=2` to obtain property `(T;FD)` of
`SL_2(Z[1/2])`. Its uniform gap applies to finite-dimensional rectangular
intertwiner spaces for any candidate exact endpoint.

The augmentation complement of the action of `PSL_2(F_p)` on its
projective line is an irreducible representation of dimension `p`:
the action is two-transitive, so the permutation commutant has dimension
two. Its character at each nonidentity torsion element is the number of
fixed projective points minus one, of absolute value at most one.

Delete `k<=12` dimensions to reach a multiple `r` of twelve. A finite
cyclic hull construction makes each modular torsion generator exact on
the retained space with precisely uniform multiplicities, while its
rectangular intertwiner error from the original irreducible is bounded
in unnormalized Frobenius norm. The full artifact proves the construction
and its bound without assuming a common invariant deleted subspace.

Adjoin a different irreducible of dimension `q>p`. A hypothetical strict
endpoint closer than `c sqrt(r/(r+q))` has nonzero intertwiners from both
the original `p`-dimensional irreducible and the `q`-dimensional one.
Irreducibility and unequal dimensions make their images orthogonal,
requiring at least `p+q>r+q` dimensions. This proves the lower bound.
Replacing the retained `r`-block by copies of the regular `A_4` endpoint
gives the matching same-stratum upper bound. Restoring the deleted
dimensions gives the separate flexible upper bound.

Bertrand's postulate supplies primes `q` between `Lp` and `2Lp` for
fixed `L`, or between `p log p` and `2p log p`. These choices give the
uniform-tube and all-positive-powers conclusions respectively.
