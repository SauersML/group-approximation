---
rg: 2
id: nonhyperlinear-from-culf-mastel-pairwise-packing
kind: route
title: Use a static positive-density word packing instead of a power-return tail
target: non-hyperlinear-group
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
  - block-encoded-acceptance-still-needs-corner-return
  - pauli-zero-atom-removes-acceptance-source-deficit
  - acceptance-return-is-one-corner-word
  - canonical-positive-density-pairwise-game-overlap-packing
  - marked-copy-collision-forces-overlap-mass
  - canonical-profile-kleene-higman
---

For the fixed game, let `alpha>0` be the canonical trace of the authenticated
packet head and let `rho<1` be the finite-matrix norm bound for the cyclic
acceptance compressor.  Choose fixed `L,M` such that

```text
M alpha>1+(M-1)rho^(2L).                                          (SP1)
```

This is possible by first taking `L` with `rho^(2L)<alpha` and then taking
`M>(1-rho^(2L))/(alpha-rho^(2L))`.

On a NONHALT instance, the pairwise compiler gives `(PGO1)` for the `M` word
translates

```text
Q_i=v_i q v_i^*.
```

Cyclicity gives

```text
tau(Q_iQ_j)=||q v_i^*v_jq||_2^2.
```

Thus `(PGO1)` upper-bounds the sum of unordered pairwise overlaps by
`M(M-1)alpha rho^(2L)/2+o(1)`.  But
`marked-copy-collision-forces-overlap-mass` lower-bounds the same sum by
`((M alpha)^2-M alpha)/2+o(1)`.  Comparison gives

```text
M alpha <= 1+(M-1)rho^(2L),
```

contrary to the choice of `M,L`.  Hence the compiled group has no canonical
normalized-HS microstate sequence.  On a HALT instance, exact perfect
completeness preserves `q!=0`.  Apply `canonical-profile-kleene-higman` to
obtain a finitely presented nonhyperlinear group.

This route consumes no coherent powers and no finite or infinite no-return
register.  Its sole new semantic gate is the static, cycle-compatible
selected-corner compiler.
