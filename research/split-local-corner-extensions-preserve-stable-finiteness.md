---
rg: 2
id: split-local-corner-extensions-preserve-stable-finiteness
kind: claim
title: A split extension with stably finite local ideal corners is stably finite
distinct_from:
  residually-p-kernels-preserve-modular-stable-finiteness: that uses separated powers of an ideal without a splitting; this uses a unital section and stably finite local corners without separation of ideal powers.
  modular-radical-does-not-lift-direct-finiteness: that excludes radical containment for a lamp ideal; this supplies another lifting mechanism that requires no radical containment.
---

Let 0->I->R->S->0 be an exact sequence of rings, with R,S unital and a
unital ring section s:S->R. Suppose S is stably finite. Suppose also that
I has idempotent local units: every finite subset of I is fixed on both
sides by some idempotent e in I, and each corner e I e is stably finite
with identity e. Then R is stably finite.

It suffices to have a cofinal family of such local units with stably finite
corners. In particular, the ideal may be a direct sum of finite-support
matrix algebras over stably finite rings. Here a finite-support matrix has
only finitely many nonzero entries, even if its indexing set is infinite.

The unital section is essential to the stated argument. This is not a
claim that stable finiteness is closed under arbitrary ring extensions.
