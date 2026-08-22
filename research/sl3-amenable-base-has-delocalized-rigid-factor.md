---
rg: 2
id: sl3-amenable-base-has-delocalized-rigid-factor
kind: claim
title: An amenable-base SL3 crossed product can have a delocalized rigid factor
distinct_from:
  haagerup-actor-amenable-basis-rigidity-fence: that uses Haagerup Fourier multipliers to force a rigid subfactor into the amenable base; this gives an explicit SL3 crossed product where a property-T subfactor intertwines into neither the base nor the actor algebra.
  amenable-group-basis-sl3-envelope: that asks for a NON-CE rigid factor inside such a crossed product; this proves only that Popa localization cannot refute the whole route, using a Connes-embeddable affine Kazhdan example.
---

Let

```text
G = Z^3 rtimes SL_3(Z),
B = L(Z^3),
M = B rtimes SL_3(Z) = L(G).
```

Then `G` is ICC with property `(T)`, so `M` is a property-`(T)` `II_1`
factor, but

```text
M not_prec_M B,                  M not_prec_M L(SL_3(Z)). (SAD1)
```

Therefore no deformation/rigidity principle based only on amenability of the
base and property `(T)` of the `SL_3(Z)` actor can force every rigid subfactor
into the base, a finite-dimensional algebra, or the canonical actor group
algebra.  Rigid structure may be genuinely spread across the amenable kernel
and the actor.

This leaves `amenable-group-basis-sl3-envelope` viable.  Haagerup stripping
fails because the infinite property-`(T)` group `SL_3(Z)` has no `c_0`
positive-definite approximants to `1`; Bernoulli malleable deformations can
give stronger conclusions for special tensor actions, but an arbitrary
action by automorphisms of an amenable group has no such deformation.

