---
rg: 2
id: steinberg-fox-marginal-pushes-are-explicit
kind: claim
title: Every five-marginal push of the Steinberg Fox rows is explicit
artifacts:
  - research/steinberg-fox-marginal-push-proof.md
distinct_from:
  steinberg-tree-cuts-are-five-marginals: that identifies the five tree-cut values, while this computes their pushforward through every coefficient of both Fox rows.
  steinberg-fox-chord-actions-are-explicit: that computes individual chord images, while this sums those images over point and plane fibers, including every exceptional fiber.
---

**ESTABLISHED.**  Let `M(f)=(P,H,A,C,T)` be the five marginals in
`(STM1)`.  For each of

```text
1, q, s, A, B, u, r, h^(-1)
```

the point and plane marginals of `L_g f` are finite, explicit expressions
in pointwise values of `f` and values of `M(f)`.  Consequently pushing both
Fox rows `(SCA4)` through `P` or `H` leaves no unevaluated tree cut or
abstract pushforward.  In particular, after putting `g=(1-q)f`, the
apparently mixed term `L_u g` is an explicit four-case pointwise slice
system on both the point and plane charts.

This reduces `steinberg-fox-recurrence-forces-zero-marginals` to a finite
closed system in `f,P,H,A,C,T`; it does not by itself prove that its only
marginal solution is zero.

DERIVATION
steinberg-fox-marginal-push-proof
