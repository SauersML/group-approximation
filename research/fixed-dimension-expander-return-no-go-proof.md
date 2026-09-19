---
rg: 2
id: fixed-dimension-expander-return-no-go-proof
kind: route
title: Evaluate the alleged proper return on the exact amplified Weyl strategy
target: dimension-expander-sampler-is-not-a-fixed-proper-return
requires:
  - trace-cyclic-triangle-balances-independent-return-gauges
---

For fixed `n`, take the standard finite-dimensional Weyl representation
satisfying every sampled Pauli relation, the exact D8 spin representation,
and any common spectator amplification.  All relator defects of the fixed
sampler vanish and `H` remains nonzero.

If `(TCT2)` held with zero error, cyclicity would give
`tr(H-G_0)=0`; if `(TCT3)` held, it would give `tr(G_1)=0`.  Together with a
zero-error balance edge `(TCT4)`, the established triangle checksum gives
`tr(H)=0`, contradicting the model.  The same contradiction applies to the
common-gauge specialization `(TGR2)--(TGR3)`.

Spectator amplification shows that increasing matrix dimension never
removes this exact countermodel at fixed `n`.  Only a single presentation
which simultaneously activates unbounded `n` can turn the sampler's
dimension lower bound into a finite-matrix contradiction.

