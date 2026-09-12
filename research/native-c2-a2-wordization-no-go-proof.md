---
rg: 2
id: native-c2-a2-wordization-no-go-proof
kind: route
title: Count the C2 double coset and compute the unipotent covariance floor
target: native-c2-hecke-corner-cannot-wordize-the-a2-average
requires:
  - native-a2-two-path-average-is-not-an-ordinary-word-compression
  - sl3-one-over-forty-two-packet-is-external-or-folded
  - raw-denominator-incidence-kills-off-diagonal-shell-orbit
---

Expansion of `(1+c)g(1+c)` gives `(CHC4)`.  The standard double-coset count

```text
|KgK|=|K| [K:K intersect gKg^(-1)]
```

is four unless `g` normalizes `K`, in which case it is two and the two terms
differ by the involution `c`.  Since `x_23(2)` has infinite order, neither
case yields the desired path support.

Canonical trace gives `(CHC8)`.  Finally diagonal conjugation sends
`x_23(2)` to `x_23(-2)`, so `cd` and `dc` are distinct group elements.
Their two coefficients in `[q,d]` are `1/2` and `-1/2`; orthonormality of
the group basis gives the exact squared norm `1/2` in `(CHC9)`.

