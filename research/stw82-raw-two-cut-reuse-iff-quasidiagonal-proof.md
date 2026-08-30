---
rg: 2
id: stw82-raw-two-cut-reuse-iff-quasidiagonal-proof
kind: route
title: Identify asymptotically projectional quasicentral cuts with quasidiagonal extensions
target: stw82-raw-two-cut-reuse-iff-quasidiagonal
requires:
  - stw82-complementary-cutdowns-merge-iff-near-projections
---

If `(p_n)` is a quasicentral approximate unit of projections, take
`h_n=a_n=p_n` and `b_n=1-p_n`.  This proves (1) implies both (2) and (3).

Conditions (2) and (3) are equivalent by
`stw82-complementary-cutdowns-merge-iff-near-projections`, but it is useful
to retain the construction which identifies the extension property.  Put

```text
eta_n=norm(h_n-h_n^2).
```

Under (2), `eta_n -> 0`.  For all sufficiently large `n`, functional
calculus gives

```text
p_n=chi_[1/2,1](h_n),
norm(p_n-h_n)
 <= (1-sqrt(1-4 eta_n))/2 -> 0.                       (Q3)
```

Although this functional calculus is performed in the unitization, its
cutoff function vanishes at zero.  Hence `p_n` belongs to `C*(h_n)`, and
therefore to the ideal `I`.

The almost-idempotent relation makes these projections increasing, a point
which norm closeness alone would not supply.  Indeed
`h_(n+1)h_n=h_n=h_n h_(n+1)`, and functional calculus first gives

```text
h_(n+1)p_n=p_n=p_n h_(n+1).
```

Thus `h_(n+1)` is the identity on the range of `p_n`, so
`p_n <= chi_[1/2,1](h_(n+1))=p_(n+1)`.

The norm perturbation preserves both properties required of the approximate
unit.  For `x in I` and `e in E`,

```text
norm(p_n x-x)
 <= norm((p_n-h_n)x)+norm(h_n x-x) -> 0,

norm([p_n,e])
 <= 2 norm(p_n-h_n) norm(e)+norm([h_n,e]) -> 0.        (Q4)
```

Thus `(p_n)` is an increasing approximate unit of projections for `I`,
quasicentral relative to `E`, proving (2) implies (1).  Finally, (3) implies
(2) from the
quantitative estimate

```text
norm(h_n(1-h_n))
 <= 2 max(norm(a_n-h_n),norm(b_n-(1-h_n))).           (Q5)
```

No nuclearity, finite-dimensionality, stability, essentiality, or Busby
fullness is used.  Separability is used only for the sequential formulation.
