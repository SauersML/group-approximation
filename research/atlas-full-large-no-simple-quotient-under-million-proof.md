---
rg: 2
id: atlas-full-large-no-simple-quotient-under-million-proof
kind: route
title: Exhaust the complete GAP simple-group catalogue after the 360 divisibility reduction
target: atlas-full-large-no-simple-quotient-under-million
requires:
  - atlas-full-large-simple-quotients-inject-three-vertices
  - atlas-full-large-finite-escape-has-simple-local-factor
---

Let `Gamma_box` be the six-generator presentation in
`experiments/atlas_a4_full_large_all_simple_under_million.g`.  By
`atlas-full-large-simple-quotients-inject-three-vertices`, any nonabelian
simple quotient `S` contains injected marked subgroups of orders `60`, `36`,
and `24`.  Hence

```text
360 = lcm(60,36,24) divides |S|.
```

The forward fan does not improve this to `720`: its two order-four normal
module kernels survive all local intersection tests, with quotient
`C3 x A4`.  Thus `360`, rather than `720`, is the correct unconditional
filter.

GAP 4.14 (through Sage 10.7) guarantees that
`AllSmallNonabelianSimpleGroups([1..999999])` is the complete list of
nonabelian simple groups in that order range.  Filtering by divisibility by
`360` leaves exactly

```text
A6, A7, M11, A8, PSL(3,4), O(5,3), M12, PSU(3,5),
PSL(2,71), A9, PSL(2,64), PSL(2,81), PSL(2,89),
M22, HJ, O(5,4).
```

For each target, `GQuotients(Gamma_box,S)` returns the empty list.  The exact
orders and class counts are frozen in the JSON artifact.  Therefore no such
`S` has order below one million.

Finally, `atlas-full-large-finite-escape-has-simple-local-factor` proves that
any finite quotient faithful on all four marked vertices admits a nonabelian
simple quotient with the three automatically injected vertices.  Its simple
composition factor therefore has order at least `10^6`.
