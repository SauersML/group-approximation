---
rg: 2
id: coherent-sequential-schur-tape-payment-proof
kind: route
title: Track full type vectors pairwise and apply the oriented half-return identity
target: coherent-sequential-schur-tape-payment
requires:
  - toeplitz-schur-bcs-shift-amalgam
  - schur-rank-output-is-not-a-scalar-selector
  - hnn-conjugacy-cannot-return-schur-morita-multiplicity
  - uniform-relative-clifford-tape-cell
  - shared-overlap-controls-packet-multiplicity-vector
  - oriented-schur-restriction-mass-identity
  - oriented-schur-child-branching-identity
  - fanizza-bcs-polynomial-doubling-tape
  - marked-hs-separation-forces-spectral-density
---

Fix a matrix tuple with total squared relator energy `E`. At level `n`, apply
uniform relative-cell exactification only to the new fixed packet cell. The
polynomial word derivations and `(FDB2)` give correction parameters bounded
by

```text
eta_n+zeta_n <= C(n+1)^k E^(1/2).                              (1)
```

The constants do not depend on the accumulated Clifford rank.

For each incidence between the output restriction of cell `n` and the input
packet of cell `n+1`, both exact representations approximate the same original
shared selector/prefix words. Apply
`shared-overlap-controls-packet-multiplicity-vector`. If `mu_n^out` and
`mu_(n+1)^in` are their complete weighted irreducible type vectors, then

```text
||mu_n^out-mu_(n+1)^in||_(weighted 1)/d
 <= C'(n+1)^k E^(1/2).                                        (2)
```

This comparison is made on the full type vectors, not by retaining a chosen
intersection subspace. Consequently a corner discarded by one polar
alignment cannot re-enter uncharged through another context: any such return
changes the next full multiplicity vector and is counted again in `(2)`.
There is no cyclic choice or holonomy to make.

The incidence used here cannot be an ordinary HNN subgroup conjugacy:
`hnn-conjugacy-cannot-return-schur-morita-multiplicity` proves that such a
conjugacy preserves rather than doubles multiplicity. Clause 3 of the open
shift-amalgam input must therefore supply a proper corner, projective
cocycle, or other genuinely Morita return before `(2)` can be invoked.

Orient each local rank compiler so its Boolean predicate is `1` exactly on
the selector sectors satisfying the corresponding propagation relation in
`(FDB1)`. Let `a_n` be the normalized marked multiplicity functional of the
input type vector at level `n`; include the fixed simple dimensions in the
functional, so `0<=a_n<=1`. Applying `(OSR1)` and then `(2)` gives

```text
a_n <= (1/2)a_(n+1)+(1/2)b_n+C'(n+1)^k E^(1/2),                (3)
```

where `b_n` is normalized inactive-sector mass. Equivalently, and in the
actual Toeplitz placement more canonically, use `(OCB3)` for the compressed
`Q` child: its two active copies carry distinct `q_(N+1)` branch labels and
already lie on the tail side of the compressor.

The inactive sectors are precisely the forbidden truth assignments for the
finite relation menu used to decompose `(FDB1)`. Clause 4 of the shift-amalgam
compiler wires every such decomposition term to an adjacent packet return.
Fixed-length telescoping from the original shared selector words to the
locally exact packet, the multiplicity discrepancy estimate `(2)`, and the
polynomial decomposition bound `(FDB2)` therefore give

```text
b_n <= C''(n+1)^k E^(1/2).                                    (4)
```

This step uses the original words before contextwise correction, so no global
joint PVM or classical popular assignment is assumed. Combining `(3)` and
`(4)` is `(SDL2)`.

At level zero, apply the marked spectral-density lemma to the involution word
encoding `x_D`, and transfer its carrier through the fixed first packet
exactification. The discarded and relator-error mass is `O(E^(1/2))`, so for
fixed `c,K>0`,

```text
a_0>=c||w-I||_2^2-K E^(1/2),                                  (5)
```

which is `(SDL1)`. Equations `(3)--(5)` prove all clauses of the target.
