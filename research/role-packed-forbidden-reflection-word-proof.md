---
rg: 2
id: role-packed-forbidden-reflection-word-proof
kind: route
title: Compare the aggregate packet density with the two possible canonical traces of a group reflection
target: role-packed-forbidden-reflection-is-not-a-group-word
requires: []
---

The maximal diagonal subgroup of the extraspecial role packet has order
`2m` and contains `J`.  The context subgroup for a `k_i`-variable assignment
has order `2^(k_i+1)` and has the same central involution.  Their central
product therefore has order

```text
(2m)2^(k_i+1)/2=m2^(k_i+1).
```

The compatible role-and-assignment character idempotent is exactly
`R_iP_i`; the coefficient of the identity in a finite-group character
idempotent is the reciprocal of the group order.  This proves `(RFW1)`.
Orthogonality of the role atoms gives additivity.  Since every context is
nonempty, `k_i>=1`; since `m>=M`, `(RFW2)` follows.

If `(RFW3)` held, then `g^*=g` and `g^2=1`.  Faithfulness of the canonical
trace on the group algebra gives trace zero for every nonidentity group
element and trace one for the identity.  Taking traces in
`B_f=(1-g)/2` therefore permits only `tau_G(B_f)=1/2` or `0`, contradicting
the strict interval in `(RFW2)`.

