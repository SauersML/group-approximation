---
rg: 2
id: coset-local-decoders-force-gated-domination-proof
kind: route
title: Project a local left inverse onto the subgroup component to get a two-sided unit, then run the unique-inverse union bound
target: coset-local-decoders-force-gated-domination
requires: [gated-diagonal-linear-deficits-force-kaplansky-failure]
artifacts:
  - research/artifacts/coset-local-decoders-gated-domination-2026-09-17.md
---

This is a direct proof in Sections 1-4 of the artifact.

- **Lemma 1.**
  - `F_q[G]` is free over `F_q[H]` on coset representatives, with `1` a representative.
  - From `a = c σ` and `σ (T c) = 1`, the identity component gives `σ b_1 = 1` in `F_q[H]`.
  - Direct finiteness of `F_q[H]` makes `σ` a unit, so `T = σ^{-1} c^{-1}`. Case (b) is the mirror
    image with right modules.
  - Finite `H` is directly finite by dimension counting.
- **Theorem 2.** Steps 1-3 of Theorem 3 in the prerequisite's artifact:
  - Lemma 2 (recovery criterion), which holds on every pattern;
  - the unique inverse, now given by unit-ness instead of global direct finiteness;
  - the union bound with stationarity.
- **Corollary 3.** Theorem 1 (exact split) and Proposition 5 (abelian homomorphic pointers have
  `gap(J) <= 0`) of the prerequisite, both valid on every incidence pattern.
  - Shared pointer sets force a finite left coset of the setwise stabilizer, which acts freely on the
    pointer positions.
- **Corollary 4.** The contrapositive, applied with `H = <d^{-1} supp T_i>` and `H = <c^{-1} supp a>`.
