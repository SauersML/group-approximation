---
rg: 2
id: modular-radical-does-not-lift-direct-finiteness
kind: claim
title: The lamp augmentation ideal is not radical, so direct finiteness does not lift along it
distinct_from:
  direct-finiteness-not-inherited-by-quotients: that is the general permanence failure, and it names descent modulo an ideal inside the Jacobson radical as the one legal quotient argument; this shows that legal argument's hypothesis fails for the lamp kernel of a modular wreath product, which is exactly where one wanted to use it.
  kun-thom-wreath-stably-finite: that is the open dividend question for the Kun--Thom groups; this is one named bridge to it, proved dead, and says nothing about whether the answer is yes.
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
since `1 + J` consists of units.  That exception is the whole reason one
hopes the locally finite lamp kernel is harmless, and it is most plausible in
the lamp characteristic, where `omega(k[N])` is a nil ideal of `k[N]`.  It is
false there.

The witness is graded, not exotic: `k[W]` is graded by lamp degree with
degree-zero part `k[G]`, `u` is homogeneous of degree one, `u^d != 0` for
every `d` because the sites `x, gx, ..., g^(d-1)x` are distinct, and the only
candidate inverse of `1 - u` is the infinite sum of the `u^d`.  The smallest
instance is the lamplighter `Z/2Z wr Z` over `F_2` with `u = y_0 t`.

## What it does not say

It does not say `k[W]` fails to be stably finite, and it does not say
`J(k[W])` is small.  It says the one-line lifting argument is unavailable and
that a replacement must control `1 + M_n(omega(k[N])k[W])` on its own terms.

The other standard route is blocked by a theorem already in this graph: for
`char k != p` the lamp algebra is the algebra of locally constant functions on
`{+1,-1}^(G/Gamma)`, so `k[W]` is the algebraic crossed product by the
generalized Bernoulli action of `G` on `G/Gamma`, and Kun--Thom's Corollary D
(`kun-thom-nonsofic-wreath`) says that action is not sofic.  Modular
characteristic loses the radical, non-modular characteristic loses the
approximation.
