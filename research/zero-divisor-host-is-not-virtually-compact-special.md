---
rg: 2
id: zero-divisor-host-is-not-virtually-compact-special
kind: claim
title: A zero-divisor host embeds in no torsion-free virtually compact special group or compact 3-manifold group, while Kazhdan hosts survive
distinct_from:
  zero-divisor-support-subgroup-host-constraints: that forbids unique products, elementary amenability and, in characteristic zero, Strong Atiyah; this adds the geometric exclusions over every field and shows that infinite Kazhdan hosts escape them.
  fisher-sanchez-peralta-special-and-3-manifold-domains: that is the imported division-ring embedding theorem; this is its consequence for where a counterexample to the zero-divisor conjecture can live.
---

**ESTABLISHED.** Let `k` be a field, `G` a torsion-free group, and
`alpha, beta` nonzero in `k[G]` with `alpha beta = 0`. Put
`H = <supp alpha ∪ supp beta>`. Then:
1. `H` is not a subgroup of any torsion-free group that is virtually the
   fundamental group of a compact special cube complex;
2. `H` is not a subgroup of the fundamental group of any compact 3-manifold.

So, over every field and in addition to
`zero-divisor-support-subgroup-host-constraints`, a counterexample cannot live
in:
- torsion-free cubulated hyperbolic groups, which are virtually compact special
  by Agol;
- right-angled Artin and Coxeter groups, or their subgroups;
- torsion-free 3-manifold groups.

**Kazhdan hosts are not excluded.** An infinite group with property (T) is
never virtually compact special. So infinite torsion-free Kazhdan groups, for
example `E_3(3)` in `SL_3(Z)` (`e33-balls-have-no-small-zero-divisors`), remain
admissible hosts for every field.

Graphical small-cancellation hyperbolic groups without unique products
(Rips--Segev, Steenbock) are excluded exactly when they are cubulated. That was
not checked here.

DERIVATION
[[zero-divisor-host-not-special-proof]]
