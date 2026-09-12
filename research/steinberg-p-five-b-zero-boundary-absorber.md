---
rg: 2
id: steinberg-p-five-b-zero-boundary-absorber
kind: claim
title: The complete p=5 b=0 Y system and anchor X rows leave the boundary scalar
artifacts:
  - research/steinberg-p-five-b-zero-boundary-absorber-proof.md
invalidates:
  - steinberg-p-five-kappa-from-b-zero-anchor
distinct_from:
  steinberg-y-anchor-leaves-one-boundary-mode: that isolates the uniform exceptional Y mode; this gives an exact characteristic-five absorber for a larger subsystem including every b=0 Y row and every X(1,0,c) row.
  steinberg-flag-fox-map-is-injective-at-p-three: characteristic three has a cancelling adjacent-fiber cascade absent from this p=5 subsystem.
---

**ESTABLISHED FIREWALL.**  Over `F_5`, the full system consisting of every
`Y(a,0,c)` row and every `X(1,0,c)` row has a solution for every prescribed
boundary scalar `kappa`.  In projective reciprocal coordinates the complete
`b=0` system is

```text
(w_a-w_(a+3))(y)-(w_a-w_(a+3))(y+a+3)
 +w_(3a)(2y)-w_(3a)(2y+1)=0.                         (P5BA1)
```

It admits the anchor `w_1=kappa` on affine points, `w_1(infinity)=0`, with
every other `w_a=0`.  A single explicit `b=2` fiber absorbs all five anchor
`X` rows.  Hence neither the complete `b=0` Y cascade nor its previously
derived residual can force `kappa=0`.  Any characteristic-five marginal
proof must use at least one additional row with `b!=0` outside that anchor
subsystem.

DERIVATION
steinberg-p-five-b-zero-boundary-absorber-proof
