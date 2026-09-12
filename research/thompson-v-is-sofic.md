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
- **Full-group soficity theorems.** Dead for `V` (lane `thompson-v-soficity`; see
  `research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md`, Section 3,
  sources read from the PDFs).
  - Ma, arXiv:2110.11548v1, Theorem 7.5, needs a Følner sequence for the groupoid. The Cuntz
    groupoid has none (`cuntz-groupoid-admits-no-folner-sequence`), so that theorem cannot
    certify `V`.
  - The LEF theorems for full groups (Grigorchuk--Medynets; Ma, arXiv:2209.00580v4) cannot
    contain `V`, which is not LEF.
  - Models with an almost-equivariant coordinate map to the Cantor set keep a fixed proportion of
    boundary, with any multiplicity or internal state (artifact Corollary 3.3).
- **Stability dictionary.** By `thompson-v-sofic-iff-not-permutation-stable`, this claim is the
  failure of permutation stability of `V`, in any of Bradford's four senses. Bradford,
  arXiv:2211.15249v2, p. 4, lists `V` among full-group relatives "not known to be sofic", and reads
  his results as evidence that `V` is stable, that is, against this claim.
