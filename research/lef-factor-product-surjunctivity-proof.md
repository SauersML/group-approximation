---
rg: 2
id: lef-factor-product-surjunctivity-proof
kind: route
title: Embed finite pieces of the product into the surjunctive factor times a finite group
target: products-with-lef-factors-preserve-surjunctivity
requires:
  - surjunctivity-is-a-commensurability-invariant
  - strict-pairs-transfer-to-table-realizations
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Section 2 of the artifact.

1. For a finite `F ⊆ G x K`, a local embedding `ψ` of its projection `F_K` into a finite group `L` gives the
   injective map `id x ψ: F -> G x L`. It preserves every product of `F` that lies in `F`, because
   products are coordinatewise.
2. `G x L` contains `G` with index `|L|`, so it is surjunctive by commensurability invariance.
3. Corollary 1 of the table-realization theorem then makes `G x K` surjunctive.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 6.2 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
