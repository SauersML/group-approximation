---
rg: 2
id: thompson-v-is-sofic
kind: claim
title: Thompson's group V is sofic
refuted_by:
  - thompson-v-not-sofic
distinct_from:
  thompson-v-not-sofic: that is the negation of this claim, whose establishment would refute it.
  thompson-v-hyperlinear: that is the normalized-HS approximation property of V; this is the Hamming statement, which implies that one.
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**OPEN.** Thompson's group `V = G_(2,1)` embeds in the universal sofic group.

Consequences:
- `V` is surjunctive (`thompson-v-surjunctive-from-soficity`);
- every modular group algebra of `V` is stably finite
  (`thompson-v-stable-finiteness-from-soficity`). That kills
  `thompson-v-ternary-swap-idempotent-is-full` and the linear route into `thompson-v-nonsurjunctive`.

## Attempts

- **Exact models.** Dead: `V` is not LEF (`thompson-v-not-lef`), so a sofic approximation
  cannot come from local embeddings into finite groups.
- **Truncating the Cantor action.** Dead: `thompson-v-cantor-orbits-have-no-folner-sets`. Every
  finite point set keeps a fixed fraction of boundary.
- **One-word form.** By `thompson-v-character-simplex`, soficity is decided by whether one
  fixed nontrivial word can move almost all points in models of small defect (see
  `thompson-v-not-sofic`). No construction reaches that.
- **Haagerup property.** `thompson-v-has-haagerup-property` supplies proper affine isometric
  actions, not permutation models. No passage from a-T-menability to soficity is known.
