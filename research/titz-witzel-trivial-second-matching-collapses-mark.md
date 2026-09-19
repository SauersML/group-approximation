---
rg: 2
id: titz-witzel-trivial-second-matching-collapses-mark
kind: claim
title: A trivial second matching quantitatively collapses the marked word in the seven-relator Titz--Witzel gate
distinct_from:
  titz-witzel-sofic-gate-has-only-seven-relators: That reduces the gate to two exact involutions and five approximate coupling equations; this proves that one of those involutions must have macroscopic support in every positive solution.
  titz-witzel-cyclic-affine-ansatz-has-linear-defect: That computes all five defects in one affine family; this gives a dimension-independent inequality for every choice of the other matching and the arbitrary permutation when the second matching is trivial.
---

**THEOREM.**  Use the seven-relator variables `(c,e,r)` and words
`Y,X,A',B',D',F',S',H'` from `(TW8)`.  Let `c,e,r` be permutations of a
finite set, assume `c^2=1` and `e=1`, and denote by

```text
delta_3=d_H(A' e D' F',1),       delta_4=d_H(D' F' e H',1)             (TEM1)
```

the defects of the third and fourth coupling relators.  Then

```text
d_H(Y^8,1) <= 8 delta_3 + 16 delta_4.                                 (TEM2)
```

Consequently no solution of the marked gate can have `e_n=1` at every
stage.  More generally, it cannot have `d_H(e_n,1)->0`: replacing `e_n` by
the identity changes every fixed word in `(TW8)--(TW9)`, including `Y_n^8`,
by `o(1)`, after which `(TEM2)` applies.

One completely explicit version, now allowing arbitrary involutory `e`, is

```text
d_H(Y^8,1) <= 8 delta_3 + 16 delta_4 + 296 d_H(e,1).                  (TEM3)
```

Thus a positive solution requires both sparse relator defects and a second
exact matching `e_n` with support bounded below by a positive proportion
along the marked subsequence.

---

### Proof

titz-witzel-trivial-second-matching-proof
