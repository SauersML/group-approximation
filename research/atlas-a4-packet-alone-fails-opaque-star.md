---
rg: 2
id: atlas-a4-packet-alone-fails-opaque-star
kind: claim
title: Exact regular A4 packet coherence alone leaves an order-two/order-four opaque-star mismatch
artifacts:
  - experiments/atlas_a4_opaque_star_regular_screen.py
distinct_from:
  atlas-a4-normal-certificate-compiler: that target may use the asymptotic collision-19243 hypothesis as well as the packet network; this gives an exact regular-margin countermodel when collision is omitted and therefore forces collision into any transport proof.
  atlas-a4-four-cycle-trace-compiler: that asks only for scalar trace transfer under the joint packet-and-collision hypotheses; this detects failure of operator conjugacy already at the second spectral moment under the packet alone.
---

There is an exact regular `A4` packet network with all non-tree stable letters
equal to one for which the four regular-chart covariance opcodes have group
orders

```text
(ord V(t01),ord V(t12),ord V(t23),ord V(t30))=(4,4,2,2). (A4-ORD-PROFILE)
```

In particular, with hub `b=t23`,

```text
inf_(A unitary) ||V(t01)-A V(b) A^*||_2 =1,
inf_(A unitary) ||V(t12)-A V(b) A^*||_2 =1.             (A4-ORD-GAP)
```

Thus the exact packet and zero stable-letter error do not imply even one of
the two displayed opaque transports.  Collision `19243` is essential not only
for the weaker scalar trace transfer but also for operator-valued opaque-star
transport.  In particular a pointwise repair of `(A4-STAR-1)` must either put
the collision residual on its right-hand side or use the collision hypothesis
in a genuinely asymptotic compactness argument; no packet-path telescoping
bound of the form `C eta` can hold on all exact regular packet networks.

The obstruction is spectral, not merely a failure to find the canonical A8
conjugator.  In a regular representation an element of order `m` has the
uniform spectral measure on the `m`th roots of unity.  The order-two and
order-four measures have optimal squared chordal matching cost one, which is
exactly `(A4-ORD-GAP)` and is invariant under arbitrary external
amplification.
