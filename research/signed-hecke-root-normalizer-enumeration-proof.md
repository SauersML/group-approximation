---
rg: 2
id: signed-hecke-root-normalizer-enumeration-proof
kind: route
title: Enumerate the signed binary transvection group and test all root conjugates
target: signed-hecke-normalizer-has-eight-external-root-returns
requires:
  - literal-whiteheads-give-gauged-moving-bridge-table
---

Represent a binary `7` by `7` matrix by its seven bit-packed rows.  Starting
from the identity, breadth-first multiplication by the ten involutions in
`(ERN1)` produces exactly `8192` matrices.  Carry a bit which is one on the
first three generators and zero on the last seven.  Every repeated matrix
is reached with the same bit, verifying at the same time that `lambda_0` is
a well-defined character on the enumerated group.

For every ordered pair of distinct coordinates `(s,t)`, form
`n_(s,t)=I+e_t e_s^*`.  Since it is an involution, it normalizes the signed
pair exactly when, for every one of the ten generators `g_j`,

```text
n_(s,t) g_j n_(s,t) in L_0,
lambda_0(n_(s,t) g_j n_(s,t))=lambda_0(g_j).           (1)
```

The exhaustive test gives `21` solutions.  Membership lookup in the same
`8192`-element table leaves precisely the eight external solutions in
`(ERN2)`.  The deterministic calculation, including all cardinality and
list assertions, is recorded in
`experiments/signed_hecke_root_normalizer_audit.py`.

Finally, the ordinary composable-root relation gives

```text
[x_(t,k)(a),x_(k,s)(b)]=x_(t,s)(ab).
```

Substitute `a=t_0`, `b=s_0` and use the defining Leavitt identity
`t_0s_0=1` to obtain `(ERN3)`.  Since every listed transvection preserves
the signed pair, it preserves its Reynolds idempotent.  Its square is one,
so after the fixed label action is removed its arbitrary commutant factor is
an involution, proving `(ERN4)`.
