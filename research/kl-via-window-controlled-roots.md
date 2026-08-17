---
rg: 2
id: kl-via-window-controlled-roots
kind: route
title: Exactify window-controlled approximate roots in an ultraproduct
target: kervaire-laudenbach-nonsingular-conjecture
requires: [window-controlled-finite-dimensional-root-theorem]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

The shape of the hyperlinear proof, with its hypothesis replaced by the
prerequisite.

Fix `G`, a nonsingular `w`, and a finite `F <= G \ {1}`.  Apply the
prerequisite along a sequence `eps_k -> 0` to get maps `rho_k` on windows
`W_k` increasing to `G` and roots `T_k`.  Because the null sequences form a
conjugation-stable two-sided ideal, the metric ultraproduct along a free
ultrafilter is a group, the `rho_k` assemble to a homomorphism `rho` on `G`,
the window condition keeps every partial product inside the controlled
region so that multiplicativity survives the passage, and separation on `F`
survives because it is asserted uniformly.  The exact relation
`w(rho, T) = 1` holds in the ultraproduct, where `T` is the class of the
`T_k`.

So `G_w` acts with `G` faithful on `F`, and letting `F` exhaust `G` gives
injectivity of `G -> G_w`.

## What this route does not do

It does not supply the roots, and it is not a reduction of the conjecture to
anything smaller — the prerequisite is a strong statement and, read in the
Hilbert--Schmidt metric, is strictly harder than the conjecture (see the
first attempt recorded on the prerequisite).  The route exists to fix the
target of that lane precisely: whoever proposes an approximation-theoretic
proof must produce the three bullets, and this is where they would be spent.

The step that this route makes explicit, and that
`overgroup-room-does-not-supply-a-root` shows cannot be skipped, is the
production of `T_k`.  Everything else here is ultraproduct bookkeeping.
