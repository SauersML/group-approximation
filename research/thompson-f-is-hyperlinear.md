---
rg: 2
id: thompson-f-is-hyperlinear
kind: claim
title: Thompson's group F is hyperlinear
refuted_by:
  - thompson-f-is-not-hyperlinear
distinct_from:
  thompson-f-is-sofic: that is soficity, which implies this claim; a nonsofic F could still be hyperlinear.
  thompson-v-hyperlinear: that is hyperlinearity of V, which implies this claim because F <= V.
---

**OPEN.** Thompson's group `F` embeds in a tracial matrix ultraproduct `prod_omega (M_n, tr_n)`.

**Equivalent form** (`thompson-f-hyperlinear-iff-relator-system-hs-unstable`): there are `epsilon > 0`
and unitaries `(U_n, W_n)` satisfying both relators of `F` up to `delta_n -> 0` in normalized
Hilbert--Schmidt norm with `||U_n W_n - W_n U_n||_2 >= epsilon`.
