---
rg: 2
id: residually-finite-actions-give-matricial-crossed-products
kind: claim
title: The algebraic crossed product of a minimal topologically free residually finite Cantor action embeds in an algebraic matrix ultraproduct
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that is the case Gamma = Z through return words; this is every residually finite action of every countable group.
  free-minimal-crossed-products-are-simple-with-rank-models: that gives approximate Følner rank models for Z^d; this gives exact algebraic embeddings under residual finiteness, which aperiodic SFTs lack.
  extensions-of-aperiodic-sfts-are-not-residually-finite-actions: that is the negative side (no residual finiteness); this is what residual finiteness buys at ring level.
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let a countable group `Γ` act minimally and topologically freely on
the Cantor set `X`, and suppose the action is residually finite (Kerr–Nowak; Ma arXiv:2209.00580,
`defn: residually finite action`). Let `k` be a field and `R = LC(X,k) ⋊ Γ`. Then:
1. `R` is simple (artifact Lemma 2.1).
2. `R` embeds unitally and injectively in `∏_ω M_(N_n)(k)`, with `N_n = |E_n|` the sizes of the
   finite models. The map is `Σ f_g u_g ↦ Σ diag(f_g|E_n) P_(β_n(g))`.
3. If `k = F_q`, then every finitely generated subgroup of every `GL_m(R)` is LEF. When `R` is
   finitely generated (an expansive action of a finitely generated group), `EL_n(R)` is a finitely
   generated LEF group with property (T) for `n >= 3` (`elementary-groups-over-fg-rings-have-property-t`).

This is the ring-level counterpart of Ma's Theorem C (LEF topological full groups). Density of the
models is not needed.

Route: `residually-finite-actions-give-matricial-crossed-products-proof`.
