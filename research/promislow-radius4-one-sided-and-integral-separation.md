---
rg: 2
id: promislow-radius4-one-sided-and-integral-separation
kind: claim
title: The radius-four Promislow one-sided unit census is 52 and no nontrivial residue lifts integrally
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks for a one-sided inverse in a modular group algebra of the binary Leavitt unit group; this concerns two-sided units in the group rings of the torsion-free virtually abelian Promislow group.
  stable-finiteness-reduces-to-prime-field: that transfers a universal direct-finiteness failure between coefficient fields; this is an exact bounded-support unit census and an integral lifting obstruction.
---

Let

```text
P=<a,b | b^(-1)a^2b=a^(-2), a^(-1)b^2a=b^(-2)>
```

be the Hantzsche--Wendt (Promislow) group and let `B(4)` be the radius-four
ball for `{a^(+-1),b^(+-1)}`.

**ESTABLISHED.**  Exactly `52` nontrivial units `u in F_2[P]` have
`supp(u) subset B(4)`, with no restriction on the support of `u^(-1)`.
Of these, `36` have inverse supported in `B(4)` and the remaining `16` have
inverse of word radius exactly `5`.  Every one of the `52` units and its
inverse has support size `21`; the `16` escaping units form two orbits of
size `8` under the automorphisms preserving the standard symmetric
generating set.

Moreover, if `u in Z[P]^x` and `supp(u) subset B(4)`, then its reduction
modulo two is a trivial unit.  There is no coefficient-height bound and no
support bound on the inverse.  Thus none of the `52` nontrivial
characteristic-two residues lifts to an integral unit with the same
radius-four support constraint.

This settles the previously open one-sided radius-four census.  It does not
settle the full integral unit conjecture at radius four: units congruent
modulo two to a trivial unit remain possible (the paper's Case A), and the
one-sided radius-five census is also open.

DERIVATION
[[tabei-radius4-unit-census-citation]]
