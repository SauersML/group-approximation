---
rg: 2
id: digit-reading-p-edge-corona-conjugator
kind: claim
title: The digit-reading p-edge has a regular matrix-corona conjugator
distinct_from:
  machine-free-digit-reading-base-is-regular-mf: that constructs regular models of the p-free base; this asks for compatibility of the two edge embeddings in one such model.
  machine-free-digit-reading-group-is-mf: that is the resulting whole-group property; this is the exact relative matrix-model datum sufficient to prove it.
---

For the p-free base `Gamma'` of
`machine-free-digit-reading-base-is-regular-mf`, with
`d=t^-1ptp^-1` treated as its free generator, construct a regular operator-MF
realization `rho:Gamma'->U(A)`, a matrix-corona embedding `iota:A->Q`, and a
unitary `W in Q` satisfying

```text
W iota(rho(t)) W*   = iota(rho(td)),
W iota(rho(a_i)) W* = iota(rho(a_i))       for every i.
```

This is the exact compatibility datum for the final HNN edge
`<t,a_i> -> <td,a_i>`.  Shulman's amalgam criterion characterizes such
compatible embeddings but does not produce `W`; product-amalgam and central
HNN permanence theorems do not cover this shear edge.

## Attempts

Finite quotients cannot synchronize both the shift and digit refinements in
the known construction.  Strong-convergence HNN theorems assume compatible
relative expectations or edge models, which is precisely the datum above.
The remaining problem is therefore relative matrix-model conjugacy, not MF
of the base.
