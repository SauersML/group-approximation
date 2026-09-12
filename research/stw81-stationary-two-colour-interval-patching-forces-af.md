---
rg: 2
id: stw81-stationary-two-colour-interval-patching-forces-af
kind: claim
title: Stationary two-colour interval patching collapses the fibre to AF
distinct_from:
  stw81-connected-base-blocks-clopen-colour-reuse: that theorem blocks approximation of a connected base by clopen finite-dimensional subalgebras; the present theorem allows ordinary overlapping interval cutoffs and proves that two-colour reuse of a fixed fibre frame would make the fibre AF.
  stw81-z-stable-usc-fields-reduce-to-first-factor-map: that theorem identifies the missing first-factor map estimate and the constant Z-field checkpoint; the present theorem rules out the most direct two-colour construction for that checkpoint.
  stw81-finite-base-usc-fibre-product-bound: that theorem safely keeps independent base and fibre colours; the present theorem explains why simply recolouring its stationary two-by-two grid cannot reduce four colours to two for a non-AF fibre.
artifacts:
  - research/artifacts/stw81-stationary-two-colour-patching-firewall-2026-08-30.md
---

Let `D` be a separable C-star algebra, let `F_0,F_1` be finite-dimensional,
and let

```text
phi_l:F_l->D       (l=0,1)
```

be c.p.c. order-zero maps.  Let `g_0,g_1` be positive contractions in
`C(X)` with

```text
g_0(t)g_1(t)>0                                         (STP1)
```

at some point `t`.  Form the four stationary localized maps

```text
Phi_(b,l)(z)=g_b tensor phi_l(z)
  :F_l->C(X) tensor D,       b,l in {0,1}.             (STP2)
```

Suppose the four domain summands can be assigned to two global colours so
that the direct sum of all maps assigned either colour is order zero.  Then

```text
phi_0(F_0) phi_1(F_1)=0.                               (STP3)
```

Consequently `phi_0+phi_1:F_0 direct_sum F_1->D` is automatically c.p.c.
order zero.

It follows that no non-AF algebra `D` admits nuclear-dimension
approximations on every finite set which can be patched over a genuine base
overlap by this stationary two-colour scheme.  In particular, this scheme
cannot prove

```text
dim_nuc(C([0,1]) tensor Z)<=1.                         (STP4)
```

The obstruction is not to two colours abstractly.  It says that a successful
two-colour interval construction must vary the two fibre frames from patch
to patch so that their support elements rotate into orthogonal position on
overlaps.  Reusing one fixed approximation and merely permuting its colour
labels forces the forbidden AF collapse.
