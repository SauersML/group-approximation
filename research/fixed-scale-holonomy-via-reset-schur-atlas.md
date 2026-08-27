---
rg: 2
id: fixed-scale-holonomy-via-reset-schur-atlas
kind: route
title: Return the full violation-oriented Schur child through reset HNN charts
target: fixed-scale-contextual-multiplicity-holonomy
requires:
  - reset-schur-bcs-branching-atlas
  - non-ce-bcs-has-robust-approximate-energy-gap
  - finite-schur-clifford-packet-flexible-hs-exactification
  - oriented-schur-child-branching-identity
  - branch-controlled-pauli-selector-reset
  - branch-reset-amalgam-preserves-mark-and-balances-types
  - hnn-selector-chart-transport-preserves-mark-and-types
  - context-local-schur-packet-marked-extension
  - schur-violation-density-gives-contraction
  - bounded-overlap-syndrome-energy-accounting
---

Apply the robust BCS gap to the original shared words on the returned carrier.
If ordinary involution or context-commutator relators do not already pay a
constant energy, fixed-word telescoping and local packet exactification give
`(RSA1)`. The oriented child identity gives `(RSA2)` exactly. The reset
amalgam destroys the old selector center without killing the mark, and the HNN
chart edge aligns the complete post-reset branch-type vector with the next
input chart. The atlas assertion gives the bounded-overlap estimate `(RSA3)`.

Now `schur-violation-density-gives-contraction` yields

```text
a_n <= (1+beta)^(-1)a_(n+1)+C'(n+1)^k sqrt(E).
```

The contractive ladder makes the positive marked base carrier incompatible
with `E->0`. Because the functional is normalized at the fixed baseline packet
size before every reset, the larger violating simple cannot absorb the surplus
by Hilbert-dimension conservation. This supplies the recurrent fixed-scale
holonomy required by the target.
