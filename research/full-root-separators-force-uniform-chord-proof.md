---
rg: 2
id: full-root-separators-force-uniform-chord-proof
kind: route
title: Factor the trace over a matrix algebra and its relative commutant
target: full-root-separators-force-uniform-chord
requires: []
---

Normalize first so that `tau(1)=1`.  Choose matrix units `E_(ij)` for the
root `M_D(C)`.  Since `(FRT1)` and `[p,A_0]=[p,A_1]=0` imply
`p in M_D(C)' intersect N`, the projection `p` commutes with every matrix
unit.  Traciality gives, for all `i,j`,

```text
tau(E_(ii)p)
 =tau(E_(ij)E_(ji)p)
 =tau(E_(ji)pE_(ij))
 =tau(E_(jj)p).                                         (FRP1)
```

The `D` equal numbers in `(FRP1)` sum to `tau(p)`, hence each is
`tau(p)/D`.  Diagonalize an arbitrary root projection `e` by a root unitary.
Because `p` commutes with that unitary, if `rank(e)=r` then

```text
tau(ep)=r tau(p)/D=tau(e)tau(p).                        (FRP2)
```

Undoing the normalization proves `(FRT2)`.

For the chord application, `(IEC2)` partitions the source and target plus
projections into corresponding orthogonal pieces, and `(IEC3)` conjugates
each pair by a group element.  The canonical group trace is conjugation
invariant, so additivity gives

```text
tau(e_(i,s)(q+X_i)/2)=tau(e_(i,s)p).                    (FRP3)
```

Divide by `tau(e_(i,s))` and use `(FRT2)` inside the normalized corner to
obtain `(FRT3)`.  A nonconstant table contradicts `(FRT3)`, proving the
claimed extension-independent obstruction and the necessity of `(FRT4)`.
