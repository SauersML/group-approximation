---
rg: 2
id: kun-thom-stabilizer-not-co-amenable-via-infinite-index
kind: route
title: Compose the forced infinite index with the Kazhdan no-mean theorem
target: kun-thom-stabilizer-not-co-amenable
requires: [infranormal-nonnormal-has-infinite-compression-orbit, no-invariant-mean-on-coset-space]
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Two steps, no third ingredient.

1. `infranormal-nonnormal-has-infinite-compression-orbit` applied to the pair
   `Gamma <= G` — infranormal by hypothesis, non-normal by hypothesis — gives
   `[G : Gamma] = infinity`.  Property (T) is not used here; the input is
   purely the compression semigroup.
2. `no-invariant-mean-on-coset-space` applied to `G`, which has property (T)
   by the Kun--Thom hypothesis, and to the infinite-index subgroup `Gamma`
   from step 1, gives that `G` admits no invariant mean on `G/Gamma`, i.e.
   `Gamma` is not co-amenable in `G`.

Both premises are established, so the composite is too.  Note the division of
labour: (T) is what makes the mean impossible, and infranormality is what
guarantees there is an infinite-index coset space to be talking about.  A
would-be Kun--Thom pair of finite index does not exist, so there is no case
split to handle.
