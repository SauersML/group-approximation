---
rg: 2
id: canonical-marked-reynolds-intersection-proof
kind: route
title: Expand the marked adjoint trace and count quotient intersections
target: canonical-marked-reynolds-return-is-subgroup-intersection
requires: []
---

Normalize the trace on `qL(Gamma)` by `tau_q(x)=tau(qx)/tau(q)`.  Since
`tau(q)=1/2`, for a group element `h` one has

```text
tau_q(h)=delta_(h,e)-delta_(h,J),
|tau_q(h)|^2=1_(h in <J>).                             (CMRP1)
```

On the marked corner `Ad(J)=1`, so the Reynolds averages may be indexed by
the quotient groups:

```text
R_A=|Abar|^(-1) sum_(abar in Abar) Ad(abar),
R_B=|Bbar|^(-1) sum_(bbar in Bbar) Ad(bbar).            (CMRP2)
```

The normalized Hilbert--Schmidt operator trace satisfies

```text
tr_ad(Ad(h))=|tau_q(h)|^2.                             (CMRP3)
```

Use cyclicity and `R_A^2=R_A` to remove the second `R_A` in `(CMR2)`, then
expand `(CMRP2)`:

```text
Theta_w
 =1/(|Abar||Bbar|)
   sum_(abar,bbar) |tau_q(abar w^(-1)bbar w)|^2.       (CMRP4)
```

By `(CMRP1)`, a summand is one precisely when

```text
abar = w^(-1)bbar^(-1)w
```

in `Gamma/<J>`.  For every element of
`Abar intersect w^(-1)Bbar w` there is exactly one such pair, proving
`(CMR3)`.  Bounds `(CMR4)` are immediate.  Equality with `1/|Abar|` means
the intersection has size `|Bbar|`, which is exactly `(CMR6)`.

For `(CMR8)`, the intersection has size at most `|Pbar|=16`, while the
denominator is `16*32`.  Finally `tr_ad(R_P)=1/16`, again by `(CMRP2)--
(CMRP3)`, so the leakage is at least `1/32`.

