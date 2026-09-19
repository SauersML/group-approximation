---
rg: 2
id: dynamic-fano-incidence-dilation-proof
kind: route
title: Split each Fano output across its four incidence labels
target: dynamic-fano-cap-incidence-labels-are-a-reversible-dilation
requires: []
---

For every nonzero `t in F_2^3`, exactly four nonzero linear forms take value
one at `t`; each such form cuts out a four-point maximal cap.  Given the old
PVM `(p_(c,t))`, choose a bijection from the four labels incident to each
`t` onto the atoms of a four-point classical ancilla and set

```text
q_(c,t,lambda)=p_(c,t) tensor e_(c,j_t(lambda)).
```

These are mutually orthogonal and sum to one.  Summing over `lambda` gives
exactly `p_(c,t) tensor 1`, so every constraint or correlation which forgets
the label is unchanged.  Product trace is trace preserving; tensoring the
finite classical algebra preserves finite dimensionality and Connes
embeddability.  In a matrix model the equal-trace direct sum is realized by
the corresponding block-diagonal amplification.

Conversely, marginalizing any incidence PVM over `lambda` recovers an old
PVM satisfying every forgotten-label constraint.  The local label sums are
only a contextwise PVM and need be neither central nor shared, so they do not
produce a deterministic cap selector.  This proves the reversible-dilation
claim and its semantic firewall.
