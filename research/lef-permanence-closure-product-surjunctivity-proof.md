---
rg: 2
id: lef-permanence-closure-product-surjunctivity-proof
kind: route
title: Carry the fixed factor through each permanence operation as a central direct factor
target: products-with-lef-permanence-closure-factors-are-surjunctive
requires:
  - products-with-lef-factors-preserve-surjunctivity
  - surjunctivity-passes-to-subgroups
  - strict-pairs-transfer-to-table-realizations
  - finitary-split-structures-pass-to-direct-products
  - finitary-split-extension-surjunctivity-permanence
  - graph-folds-over-surjunctive-groups-are-surjunctive
artifacts:
  - research/artifacts/w3-products-permanence-closure-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Section 2 of the artifact (Theorem B′).
- **LEF factors:** the LEF product theorem.
- **Subgroups:** heredity, since `G x K'` sits inside `G x K`.
- **Local embeddings:** the general form of the LEF product theorem, through Corollary 1 of the table
  transfer.
- **Finitary split extensions:** `G x (N ⋊ B) = N ⋊ (G x B)` is finitary over `G x B`, so Theorem 0 applies.
- **Graph folds:** `G x Q` is the fundamental group of the graph of groups with vertex groups `G x Q_v` and
  edge groups `G x Q_e`. In it `G` is central and retracts, so the group splits. The fold `id x f` is
  injective on vertex groups into the surjunctive `G x K`, so the graph-fold theorem applies.

**Verification.** `w3-vf-positive` passed this route (Section 1.2–1.4 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`). The graph-fold splitting E ≅ G x Q is re-derived in 1.3. One wording point: the claim's sentence that Cl(LEF) is closed under finite direct products needs membership, not only surjunctivity; 1.4 supplies that induction.
