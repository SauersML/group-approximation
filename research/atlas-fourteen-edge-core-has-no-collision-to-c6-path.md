---
rg: 2
id: atlas-fourteen-edge-core-has-no-collision-to-c6-path
kind: claim
title: The fourteen-edge packet core has no incidence path from collision to the other C3 carrier
distinct_from:
  atlas-a4-rank-three-core: that identifies the two K2,2 components and their generated GL3(2) group; this records the consequence for every possible edge-message telescope aimed at the common-U collision operator.
  atlas-shifted-factorizations-have-independent-right-gauge: that identifies independent right-regular gauge fibers on individual shifted factorizations; this proves that even after spanning-tree gauge fixing, no packet rectangle crosses between the two components.
---

In the fourteen-word rank-three packet core, the incidence graph is exactly

```text
K_(2,2)[H_6] disjoint_union K_(2,2)[K].                (A4-NOPATH-1)
```

Every second-chart syllable of collision `q_19243` lies in the `K` component,
and its repeated first-chart involution `b_0` is not a packet vertex.  The
order-three generator `a` defining `P_6=(1+a+a^2)/3` lies in the other,
`H_6`, component.  Therefore there is no incidence path, and hence no product
of packet edge messages along a path, from `b_0` (or any collision syllable)
to `a`.

After fixing a spanning tree in each `K_(2,2)`, the complete witness-level
packet information consists of two independent rectangle holonomies, one in
each component.  Each rectangle word begins and ends in its own component;
their product is still only a disjoint pair of based loops.  In particular it
cannot telescope to either mixed covariance residual

```text
(a-1)E_K^-U^*rho(b_0)UE_K^+P_6,
E_K^-U^*rho(b_0)UE_K^+(a-1)                            (A4-NOPATH-2)
```

from `atlas-common-u-c3-compression-is-two-covariance-residuals`.

This is a fence on the proposed *path telescope*, not a counterexample to the
common-`U` matrix estimate.  The two components are coupled only because all
fourteen shifted double-coset conditions use the same literal `U` and fixed
reference alignment `R`; that coupling is absent from the incidence graph
and from independently gauged edge messages.  Consequently the next valid
attack must work directly with the simultaneous intersection of the fourteen
shifted double cosets (plus collision), rather than trace `b_0` through packet
edges.  Constructing an exact finite-dimensional point of that intersection
with nonzero `(A4-NOPATH-2)` would refute `(A4-C3-9)`; no such point is supplied
by the no-path argument.
