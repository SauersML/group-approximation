---
rg: 2
id: schur-flip-wreath-compressor-has-infinite-cocycle-rank-proof
kind: route
title: Cancel each packet cocycle by one local Pauli qubit and tensor over the new fixed sites
target: schur-flip-wreath-compressor-has-infinite-cocycle-rank
requires:
  - schur-packet-flips-realize-predicate-cocycle
  - compressor-fixed-site-growth-infinite
---

On the forbidden packet simple, `(SPF2)` gives flip implementers `Q_x,P_x`
with `Q_xP_x=-P_xQ_x`.  Choose Pauli involutions `X,Z` on `C^2`.  Then

```text
(Q_x tensor X)(P_x tensor Z)
 =(P_x tensor Z)(Q_x tensor X),
```

because the two minus signs cancel.  These operators square to one and
implement the prescribed packet automorphisms, so `(SFW2)` is a representation
of the finite semidirect product `H_f`.

In the Bernoulli tensor product, distinct sites act on distinct tensor
factors.  A site fixed by `Gamma` contributes its full local algebra to the
`Gamma`-relative commutant.  After conjugation by `s`, the same is true for
the sites in `s X^Gamma`; thus every site in the displayed difference is a
new independent local factor in the compressed relative commutant.
`compressor-fixed-site-growth-infinite` supplies arbitrarily many such sites
after one strict compressor.

On each selected site, ignore the external cancellation qubit and read the
packet implementers `Q_x,P_x`.  Their projective commutator matrix is one
copy of `H`.  Operators from distinct sites commute, so all cross entries are
zero and `n` sites give the direct sum of `n` copies, of rank `2n` over
`F_2`.

