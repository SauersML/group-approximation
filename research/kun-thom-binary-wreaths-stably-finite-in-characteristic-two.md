---
rg: 2
id: kun-thom-binary-wreaths-stably-finite-in-characteristic-two
kind: claim
title: Binary permutational wreath products over residually finite bases satisfy Kaplansky in characteristic two
distinct_from:
  kun-thom-wreath-stably-finite: that asks for every field; this settles characteristic two and leaves odd positive characteristics open.
  modular-radical-does-not-lift-direct-finiteness: the radical-containment obstruction remains true, but separated ideal powers suffice to establish this finiteness result.
  residually-p-kernels-preserve-modular-stable-finiteness: that is the general extension mechanism; this applies it to the concrete nonsofic-family question with a residually finite base.
---

For every residually finite group G, every G-set X, and every field k of
characteristic two, the group algebra

    k[(direct_sum_X C_2) semidirect G]

is stably finite, and in particular directly finite.

This settles characteristic two for the Kun--Thom wreath products with
residually finite base recorded at `kun-thom-wreath-stably-finite`,
including the explicit Theorem E groups in `kun-thom-nonsofic-wreath`.
The conclusion is independent of any nonsoficity claim or approximation
property of the action on X. It applies to arbitrary X and uses only
residual finiteness of G and the elementary abelian two-group kernel.

It does not prove full surjunctivity of these groups or stable finiteness
in odd positive characteristic. Characteristic zero was already settled
for all groups; the all-field Kun--Thom target therefore remains open
precisely in odd positive characteristics.
