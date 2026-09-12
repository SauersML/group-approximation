---
rg: 2
id: modular-radical-does-not-lift-direct-finiteness
kind: claim
title: The lamp augmentation ideal need not lie in the Jacobson radical
distinct_from:
  direct-finiteness-not-inherited-by-quotients: that is the general permanence failure; this shows that one sufficient radical-containment hypothesis fails for the lamp kernel, without excluding other lifting arguments.
  kun-thom-wreath-stably-finite: that is now established over every field; this excludes only radical containment, which neither the modular nor the all-field finiteness proof requires.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Let `p` be prime, `k` a field of characteristic `p`, `G` a group acting on a
set `X`, `N = (Z/pZ)^(X)` the restricted sum of lamps, and
`W = N semidirect G` the permutational wreath product.  If some `g in G` has
an infinite orbit on `X`, then

    omega(k[N]) k[W]   is not contained in   J(k[W]),

where `omega(k[N])` is the augmentation ideal of the lamp group algebra.
Explicitly, for `x` on an infinite `<g>`-orbit and `y_x = a_x - 1`, the
element `u = y_x g` lies in `omega(k[N])k[W]` and `1 - u` is not invertible.

**In particular this applies to every Kun--Thom nonsofic wreath product**
`W = (directSum_(G/Gamma) Z/2Z) semidirect G` at `char k = 2`, because
`infranormal-nonnormal-has-infinite-compression-orbit` supplies the element
with an infinite orbit on `G/Gamma`.

## Which bridge this burns

`k[W]/omega(k[N])k[W] = k[G]`, and for the Kun--Thom groups the base `G` is
residually finite, so `k[G]` is stably finite over every field.  Direct
finiteness does not travel backwards along a quotient in general
(`direct-finiteness-not-inherited-by-quotients`), with one standard
exception: it does descend modulo an ideal contained in the Jacobson radical,
since `1 + J` consists of units. That exception was one reason to
hope the locally finite lamp kernel is harmless, and it is most plausible in
the lamp characteristic, where `omega(k[N])` is a nil ideal of `k[N]`.  It is
false there.

The witness is graded, not exotic: `k[W]` is graded by lamp degree with
degree-zero part `k[G]`, `u` is homogeneous of degree one, `u^d != 0` for
every `d` because the sites `x, gx, ..., g^(d-1)x` are distinct, and the only
candidate inverse of `1 - u` is the infinite sum of the `u^d`.  The smallest
instance is the lamplighter `Z/2Z wr Z` over `F_2` with `u = y_0 t`.

## What it does not say

It does not say `k[W]` fails to be stably finite, and it does not say
`J(k[W])` is small. It excludes only this radical-containment argument.
There is no requirement that a replacement invert every element of
`1 + M_n(omega(k[N])k[W])`.

**Correction, 2026-09-07.**
`residually-p-kernels-preserve-modular-stable-finiteness` supplies the
replacement: the lamp augmentation powers have zero intersection, so
an inverse defect, being an idempotent in all those powers, must vanish.
Thus k[W] is stably finite whenever k[G] is, in characteristic p for these
p-lamps. In particular,
`kun-thom-binary-wreaths-stably-finite-in-characteristic-two` settles the
characteristic-two Kun--Thom case. The nonradical witness proved here
remains valid; the earlier suggestion that it prevented all modular
lifting was too strong.

The other standard route is blocked by a theorem already in this graph: for
`char k != p` the lamp algebra is the algebra of locally constant functions on
`{+1,-1}^(G/Gamma)`, so `k[W]` is the algebraic crossed product by the
generalized Bernoulli action of `G` on `G/Gamma`, and Kun--Thom's Corollary D
(`kun-thom-nonsofic-wreath`) says that action is not sofic.  Modular
characteristic loses the radical, non-modular characteristic loses the
approximation. Both proof restrictions have now been bypassed:
`rf-lamp-permutational-wreaths-satisfy-stable-finiteness` proves the
residually finite-base wreath result over every field using finite
marked-site tensors, independently of sofic approximation of the action.
