---
rg: 2
id: bernoulli-codes-descend-to-window-subgroup
kind: claim
title: A Bernoulli code whose window lies in a subgroup is almost everywhere injective exactly when its induced subgroup code is
distinct_from:
  sofic-radical-localizes-bernoulli-deficit-witnesses: that says the points of a finite deficit configuration generate a nonsofic subgroup; this is an exact equivalence for codes, reducing almost-everywhere injectivity over the group to the same property over the subgroup the window lies in.
  bernoulli-rokhlin-maximality-passes-to-subgroups: that transfers entropy maximality along subgroup inclusions; this transfers almost-everywhere injectivity of one code in both directions, through the left cosets of its window subgroup.
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Let `G` be a countable group, `K <= G`, `A, B` finite, and `f: A^K -> B` Borel. Define

    tau(x)(g) = f( (g^-1.x)|_K )   on A^G,        tau_K(z)(k) = f( k^-1.z )   on A^K.

Then `tau` is injective on a set of full uniform measure if and only if `tau_K` is.

*Proof sketch.* `tau(x)(gk)` reads `x` only on the left coset `gK`. With `z(k) = x(gk)`, the output
on `gK` is `tau_K(z)`. The product measure splits over the countably many cosets, and Fubini gives
both directions. Section 7.2 of the artifact.

**Consequence.** A measurable alphabet compression whose window generates a sofic subgroup is
impossible, since sofic groups are Rokhlin-maximal. Over `U = L_(F_2)(1,2)^x` the window of any
compression must generate a nonsofic subgroup. That matches the localization theorem, now as an
exact reduction: compression over `U` with window in `K` is the same problem as compression over `K`.

**ESTABLISHED 2026-09-12** by [[bernoulli-codes-descend-proof]].
