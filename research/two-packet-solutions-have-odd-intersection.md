---
rg: 2
id: two-packet-solutions-have-odd-intersection
kind: claim
title: Every Leavitt two-packet solution has odd support intersection and distinct conjugators
distinct_from:
  two-packet-linear-trace-vanishes: that proves the two global linear vanishings; this applies them to the full correction equation and converts the remaining trace into a support-intersection parity condition.
  two-packet-solution-requires-relative-double-coset-folding: that is a relative free-product support obstruction; this is an exact parity obstruction that applies whether or not the two double cosets fold.
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

Every solution `(x,y)` of

```text
A P_y + P_x B + P_x P_y = Delta
```

satisfies

```text
tau(P_xP_y)=1,
|supp(P_x) intersect supp(P_y)| = 1 mod 2,
x != y.
```

The first identity uses `tau(Delta)=1` and the global vanishing of both linear
terms.  The second uses `P_x=P_x^*`.  On the diagonal,
`tau(P_x^2)=epsilon(P_x)=0`, so equality of the conjugators is impossible.
