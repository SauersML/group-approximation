---
rg: 2
id: stw96-countable-zstable-filtrations-have-generators
kind: claim
title: Countably stratified Z-stable real-rank-zero algebras have generic generators
artifacts:
  - research/artifacts/stw96-mixed-rr0-extension-audit-2026-08-30.md
---

Let `A` be a nonzero separable C*-algebra of real rank zero.  Suppose that,
for some countable ordinal `gamma`, there is an increasing family of ideals
`(I_alpha)_(alpha <= gamma)` such that

* `I_0 = 0` and `I_gamma = A`;
* at every limit ordinal `beta <= gamma`,
  `I_beta` is the closure of the union of the earlier `I_alpha`; and
* every successor quotient `I_(alpha+1)/I_alpha` is `Z`-stable.

Then `A` is `Z`-stable and has generator rank one.  In particular, a generic
element of `A` is a generator.

Consequently, the conclusion holds if `A` is also nowhere scattered and has
finite nuclear dimension, and all the successor quotients in the filtration
are simple.  It therefore holds for every nonzero separable,
nowhere-scattered, finite-nuclear-dimension, real-rank-zero C*-algebra with
finitely many ideals, even when purely infinite and stably finite simple
subquotients both occur.
