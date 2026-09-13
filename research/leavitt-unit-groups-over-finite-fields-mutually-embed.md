---
rg: 2
id: leavitt-unit-groups-over-finite-fields-mutually-embed
kind: claim
title: In each characteristic p all Leavitt unit groups L_(F_q)(1,n)^x embed in one another, so their approximation problems are one problem
distinct_from:
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that proves nonsoficity of every d-ary Leavitt unit group over a finite field through a corner route; this proves the groups embed in each other, so every subgroup-closed property is decided at once for the whole family of a given characteristic.
  leavitt-algebras-l-k-1-n-are-simple: that is simplicity of the algebras; this is the resulting mutual embedding of their unit groups.
---

**ESTABLISHED** by `leavitt-unit-groups-over-finite-fields-mutually-embed-proof`.

Fix a prime `p`. For all powers `q, q'` of `p` and all `n, n' >= 2` there are
injective group homomorphisms

```text
L_(F_q)(1,n)^x  ->  L_(F_p)(1,2)^x  ->  L_(F_q')(1,n')^x .
```

**Consequence.** Let `P` be any isomorphism-invariant property of countable groups
that passes to subgroups, such as being hyperlinear, sofic, linear sofic over a
given field, weakly sofic, LEF, a-T-menable, or free of `H_3(Z)`. Then `P` holds for
one member of the family exactly when it holds for all. In particular:
- `binary-leavitt-unit-group-hyperlinear` is the hyperlinearity question for every
  `L_(F_(2^k))(1,n)^x`;
- `leavitt-unit-group-has-no-integer-heisenberg-subgroup` is the Heisenberg question
  for all of them;
- every one of these groups contains Thompson's `V`, so a positive hyperlinearity
  answer for any of them requires `thompson-v-hyperlinear`.

The "relatives `L_K(1,n)^x`" of the binary witness therefore add no new
hyperlinearity problem over finite fields. A genuinely different instance needs a
different characteristic, or an infinite coefficient field.
