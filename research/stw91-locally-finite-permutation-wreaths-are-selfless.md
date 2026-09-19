---
rg: 2
id: stw91-locally-finite-permutation-wreaths-are-selfless
kind: claim
title: Locally finite permutation wreath products of linear C-star-simple groups are selfless
distinct_from:
  stw91-finitary-permutation-wreaths-are-selfless: that requires every top-group element to have finite support; here the locally finite top group may act with infinite support, including by its regular action.
  vigdorovich-linear-selflessness: the full wreath products here contain an infinite restricted direct power and are generally nonlinear; only their finite packets are linear.
artifacts:
  - research/artifacts/stw91-locally-finite-permutation-wreath-audit-2026-08-30.md
---

Let `P` be a nontrivial countable linear group with trivial amenable radical,
let `X` be a countably infinite set, and let `L <= Sym(X)` be a countable
locally finite group.  Then

```text
W=P^(X) rtimes L
```

has selfless reduced C-star algebra.  In particular, `W` is C-star simple
and `C*_r(W)` has stable rank one and strict comparison.

The action of `L` need not be finitary.  For example, if an infinite
countable locally finite group `L` acts on itself by left translation, then
the regular wreath product `P wr L` is covered, although every nonidentity
top-group element moves infinitely many coordinates.
