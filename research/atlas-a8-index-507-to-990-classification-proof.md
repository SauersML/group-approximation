---
rg: 2
id: atlas-a8-index-507-to-990-classification-proof
kind: route
title: Audit the CFSG order formulas through A11 and apply the A8 low-index orbit list
target: atlas-a8-index-507-to-990-reaches-natural-a11
requires: []
artifacts:
  - experiments/atlas_a8_index_507_to_990_order_sieve.py
  - experiments/atlas-a8-index-507-to-990-order-sieve.json
---

Use the standard CFSG family order formulas, as collected for example in
Wilson, [*The Finite Simple
Groups*](https://doi.org/10.1007/978-1-84800-988-2), together with the
[ATLAS sporadic order table](https://brauer.maths.qmul.ac.uk/Atlas/v3/).
Between `|M23|=10200960` and `|A11|=19958400`, the complete list is

```text
L2(q), q=256,277,281,283,289,293,307,311,313,317,331,337;
U5(2), L3(8), 2F4(2)', A11.                          (SIA3)
```

Here is a short family-by-family bound establishing completeness.  For
`L2(q)`, its order formula and the two endpoints force `q<=342`; exact
prime-power enumeration gives precisely the twelve values in `(SIA3)`.
For linear groups of rank at least two, monotonicity leaves only `L3(8)` in
the interval: `L4(3)` and `L5(2)` lie below, while `L4(4)`, `L5(3)`, and
`L6(2)` lie above.  For unitary groups it leaves only `U5(2)`; `U3(8)` and
`U4(3)` lie below, while the next parameters and `U6(2)` lie above.
Symplectic and orthogonal families jump from `Sp6(2)` below the interval to
`Sp4(7)` or `O8+(2)` above it.  The exceptional order formulas leave only
the Tits group: `G2(3)` and `Sz(8)` lie below, while `G2(4)`, `Sz(32)`,
`2G2(27)`, and `3D4(2)` lie above.  The sporadic table has no group strictly
between `M23` and `A11` in this order interval.

The exact attached arithmetic replay computes every order in `(SIA3)` and
finds

```text
20160 divides |S|  iff  S=A11.                       (SIA4)
```

Lagrange therefore proves `(SIA2)`.  It remains to classify the subgroup.
Restrict the natural degree-eleven action of `A11` to `A`.  The standard
low-index subgroup list for `A8` says its only nontrivial transitive
permutation degree below twelve is eight, and that action is natural.  The
restriction is faithful because `A` is nonabelian simple, so its orbit
decomposition is

```text
8+1+1+1.                                             (SIA5)
```

Thus `A=Alt(X)` on its unique eight-point orbit.  This proves the stated
embedding classification.  The MSI replay is exact integer arithmetic and
completed in under one second on one CPU.

