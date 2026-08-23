---
rg: 2
id: mihailova-one-coset-wreath-reduction-proof
kind: route
title: Extract finitely many orbit copies and embed their diagonal product in a power of one wreath
target: mihailova-envelope-forces-one-sl3-coset-wreath
requires:
  - mihailova-sl3-restriction-is-coset-amplification
  - mixed-envelope-finitely-extracts-sl3-module-witness
---

Let `A=direct_sum_Y C_2` be the mixed coset lamp module.  A successful
property-`(T)` envelope satisfies the hypothesis of
`mixed-envelope-finitely-extracts-sl3-module-witness`, so there is a finitely
generated `F_2[L]`-submodule `A_0<A` for which `A_0 rtimes L` is
nonhyperlinear.

By `(MSR4)`, `A` is a direct sum of copies of `C`.  Each of the finitely many
module generators of `A_0` has finite support in that outer direct sum.
Therefore some finite set of orbit copies contains all of them, and

```text
A_0 < C^n,                 A_0 rtimes L < C^n rtimes L (MOR1)
```

for some `n`.  Since hyperlinearity passes to subgroups, `(MOR1)` implies
that `C^n rtimes L` is nonhyperlinear.

There is an injective diagonal-actor homomorphism

```text
C^n rtimes L -> (C rtimes L)^n,
((c_1,...,c_n),g) |-> ((c_1,g),...,(c_n,g)).           (MOR2)
```

If `W_N=C rtimes L` were hyperlinear, its finite direct power would be
hyperlinear, and then its subgroup in `(MOR2)` would be hyperlinear.  This
contradicts the preceding paragraph.  Hence `W_N` is nonhyperlinear.
