---
rg: 2
id: relative-pauli-child-split-gives-one-exit-copy-proof
kind: route
title: Use anticommutation to exchange the two spectral halves
target: relative-pauli-child-split-gives-one-exit-copy
requires:
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - predicate-rank-gate-doubles-restriction-multiplicity
  - finite-schur-clifford-packet-flexible-hs-exactification
---

The Schur-pair theorem says that on a forbidden atom the corrected relative
words centralize `A_f` and generate `M_2`; choose Pauli coordinates
`P_a=X,Q_a=Z`.  Functional calculus gives `(PCS2)`, and centralization of
`Q_a` with `A_f` makes both ranges `A_f`-invariant.

Anticommutation gives

```text
P_a Q_a P_a^*=-Q_a,
```

so conjugating `(PCS2)` by `P_a` exchanges `E_+` and `E_-`.  They therefore
have equal rank.  Their orthogonal sum is the identity on
`S_a tensor C^2 tensor C^m`, whose dimension is `2 dim(S_a)m`; each has rank
`dim(S_a)m`.  Since the `A_f` sector is the full matrix algebra on `S_a`,
each range is `S_a^(direct sum m)`.  This proves `(PCS3)--(PCS4)`.

The approximate statement uses no new rounding theorem.  Flexible finite-
group exactification supplies the exact block, and each projection in
`(PCS2)` is a degree-one polynomial in a named generator, so its normalized
Hilbert--Schmidt and trace drift is bounded by the same fixed-packet
exactification constant.
