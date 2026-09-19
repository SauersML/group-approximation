---
rg: 2
id: conditional-parent-absence-packet-exposes-relative-pauli-proof
kind: route
title: Permute the columns into a fixed core and a parent-controlled diagonal factor
target: conditional-parent-absence-packet-exposes-relative-pauli
requires:
  - clifford-commutator-rank-is-packet-dimension
---

The determinant of `(CPA1)` is `1+e`, and its fixed upper-right entry is one,
so its ranks are one and two as stated.  Permuting the two `q` columns turns it
into

```text
diag(1,1+e).
```

Thus `(p_1,q_2)` is a fixed Pauli pair, `(p_2,q_1)` commutes with it, and the
latter pair has commutator phase `1+e`, equivalently the central group element
`J z_e` in the `J=-1` convention.  Apply
`clifford-commutator-rank-is-packet-dimension` to the two diagonal factors to
obtain `(CPA2)`.  Restricting the statement to `f=1` turns `e=0` into exactly
the child-without-parent atom.
