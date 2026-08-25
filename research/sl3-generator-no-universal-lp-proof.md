---
rg: 2
id: sl3-generator-no-universal-lp-proof
kind: route
title: Promote generator-system LP through enough unitaries and contradict the known LLP failure
target: sl3-generator-system-has-no-universal-lp
requires: []
---

The unitaries in `E_S` generate `C^*(Lambda)`, so Proposition 5.6 of
Kavruk--Paulsen--Todorov--Tomforde (the enough-unitaries C-star-envelope
criterion) identifies

```text
C_e^*(E_S)=C^*(Lambda).                                           (SUN1)
```

The operator-system lifting theorem used in
`maslov-generator-complete-order-model-is-llp-strength` promotes LP of an
operator system containing enough unitaries to LLP of its C-star envelope.
Combining that implication with `(SUN1)` would give LLP of
`C^*(SL_3(Z))`.  Ioana--Spaas--Wiersma Corollary B says precisely that this
full group C-star algebra fails LLP.  Contraposition proves the claim.

