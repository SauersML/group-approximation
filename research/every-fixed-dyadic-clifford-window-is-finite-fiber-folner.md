---
rg: 2
id: every-fixed-dyadic-clifford-window-is-finite-fiber-folner
kind: claim
title: Every fixed-depth dyadic Clifford window is a finite-fiber Folner graph
distinct_from:
  depth-two-clifford-types-form-a-finite-fiber-folner-graph: that treats only the deepest two congruence layers; this proves the same obstruction for every fixed number of deepest layers.
  exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss: that gives a same-conductor loss uniform in the conductor; this shows that retaining any fixed-depth Clifford label still cannot turn the cross-conductor transition graph into an expander.
  spherical-quadrature-tensors-through-clifford-folner-windows: that tensors a spherical escape through a chosen bounded-depth type graph; this supplies the level-independent finite fiber for every fixed depth.
---

Fix `k>=1`.  For `a>=2k` put

```text
Q_a=SL_3(Z/2^a Z),
N_(a,k)=ker(Q_a -> Q_(a-k)).                            (FDC1)
```

Then `N_(a,k)` is canonically the finite additive group

```text
sl_3(Z/2^k Z),
1+2^(a-k)X <-> X mod 2^k,                              (FDC2)
```

and conjugation of `Q_a` on this kernel factors through the fixed finite
group `Q_k=SL_3(Z/2^k Z)`.  Consequently the Clifford label seen by the
deepest `k` congruence layers of an irreducible `Q_a`-module belongs to the
fixed finite set

```text
F_k=sl_3(Z/2^k Z)^hat/Q_k,                              (FDC3)
```

independently of `a`.

It follows that every transition graph which remembers only

1. the `A_2` coweight/conductor coordinate;
2. the Clifford orbit label in `F_k`; and
3. finitely many bounded-range Weyl, denominator, parahoric, inverse, or
   local-cycle incidences

is a bounded-range subgraph of `Z^2 times F_k`.  Every infinite connected
component of such a graph is amenable.  In the full transition system, full
fibers over coweight boxes give explicitly

```text
|boundary(B_R times F_k)|/|B_R times F_k|=O_k(1/R).     (FDC4)
```

Therefore **no fixed congruence depth** can prove the missing projective
transfer by a type-graph expansion argument.  A proof of
`projective-trace-square-transfer-for-sl3-pair` must retain depth growing
with the conductor, authenticate histories as distinct vertices of a
nonamenable object, or use a same-carrier interference relation not encoded
by the finite Clifford orbit label.

This is a no-go for a proof architecture, not a countermodel to the full
arithmetic presentation.  The Folner models need not extend to approximate
representations of `SL_3(Z[1/2])`.
