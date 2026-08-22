---
rg: 2
id: two-native-p3-weyl-charts-have-the-same-mackey-class
kind: claim
title: Two native p-three Weyl charts have the same Mackey class on their overlap
distinct_from:
  p3-full-parahoric-interlock-enforces-inverse-mackey-cocycle: that shows one full packet forces an inverse cocycle on multiplicity; this compares two native packet charts on their overlap and proves that the same twisted multiplicity cancels both.
  actual-parahoric-triangle-kills-abelian-correctors: that excludes abelian corrector families using the integral forty-two-chart relation module; this concerns the nonabelian projective oscillator gauge and shows why two Weyl-related charts do not create incompatible projective classes.
  fixed-holonomy-on-overlap-pays-relator-energy: that converts an already authenticated nontrivial relative holonomy into an HS floor; this computes that the relative class for two native p-three charts is trivial.
---

Let `(N_i,pi_i,L_i)` and `(N_j,pi_j,L_j)` be two level-`3^a`
Heisenberg oscillator charts related by a signed Weyl element `w`.  Let `H`
be their overlap little group, with the chart identification

```text
theta:H -> theta(H),             theta(g)=wgw^(-1).     (TWC1)
```

Choose oscillator intertwiners with multipliers `alpha_i,alpha_j`.  Transport
the first system through `w`.  The transported intertwiners implement the
second chart, so uniqueness up to scalar gives a one-cochain `b:H->T` with

```text
alpha_j(theta(g),theta(h))
 = b(g)b(h)b(gh)^(-1) alpha_i(g,h).                     (TWC2)
```

Consequently

```text
theta^* [alpha_j|_(theta(H))] = [alpha_i|_H] in H^2(H,T). (TWC3)
```

The same conclusion holds for an opposite-root chart.  Such a chart may
dualize the oscillator central character, replacing the multiplier class by
its inverse.  The p-three Weil--Maslov class used by the flux route is the
metaplectic `mu_2` class, hence has order at most two; inversion fixes it.
Thus every native Weyl/opposite-root pair has **trivial relative class** on
the canonically identified overlap.

After rephasing the second oscillator intertwiners by `b`, the two restricted
multipliers are literally equal.  One finite `alpha_i^(-1)`-twisted regular
representation on the common multiplicity reservoir then cancels both chart
systems exactly.  Hence two native p-three packet charts cannot produce a
dimension-independent overlap defect through Mackey-class incompatibility.

More generally, if two chart operator families are not identified on their
overlap, every pair of finite cocycles can be canceled on one larger reservoir:

```text
M=l^2(L_i) tensor l^2(L_j),
V_i(g)=lambda_(alpha_i^(-1))(g) tensor I,
V_j(h)=I tensor lambda_(alpha_j^(-1))(h).                (TWC4)
```

If the overlap operators are identified, exact joint cancellation is possible
precisely when the restricted classes agree after the prescribed chart
identification; `(TWC3)` verifies that condition for the native arithmetic
pair.  Therefore a surviving common-reservoir obstruction needs a
non-Weyl-related packet class, a third/global loop not reducible to pairwise
overlaps, or a separate capacity bound.  Merely taking two native parahoric
charts does not supply it.
