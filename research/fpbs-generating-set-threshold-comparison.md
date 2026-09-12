---
rg: 2
id: fpbs-generating-set-threshold-comparison
kind: claim
title: The percolation thresholds of two Cayley graphs of one group are comparable through an explicit power map
distinct_from:
  fpbs-nonuniqueness-phase-is-a-group-invariant: that asserts the nonuniqueness phase does not depend on the generating set; this proves only two-sided threshold inequalities with a power loss, which transfer a gap only when the gap has a margin.
  fpbs-relative-gap-along-any-subgroup-separates: that separates the thresholds of one Cayley graph through a relative threshold along a subgroup; this compares the thresholds of two different Cayley graphs of the same group.
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

**ESTABLISHED.** Let `S, S'` be finite symmetric generating sets of a group
`Gamma`, not containing `e`, and let `G = Cay(Gamma,S)`, `G' = Cay(Gamma,S')`.

- **Words and multiplicity.** For each pair `{s',s'^{-1}} ⊆ S'`, fix a word over
  `S` of length at most `L` representing one of them. Let `M` be the largest
  number of steps of these paths (translated over `Gamma`, doubled for
  involutions) that traverse a single edge of `G`. Then `M <= 4L|S'|`.
- **The map.** Put `phi(p) = (1 - (1-p)^{1/M})^L`.

Then:

1. **Pointwise comparison.** For all `p`, all `x, y`, and every infinite
   subgroup `I`:
   - `tau^{G'}_{phi(p)}(x,y) <= tau^G_p(x,y)`;
   - `theta^{G'}(phi(p)) <= theta^G(p)`;
   - `chi^{I,G'}_{phi(p)} <= chi^{I,G}_p`.
2. **Threshold inequalities.**
   - `p_u(G') >= phi(p_u(G))`;
   - `p_c(G') >= phi(p_c(G))`;
   - `p_c(I;G) <= phi^{-1}(p_c(I;G'))`.
3. **Nested sets.** If `S ⊆ S'`, then `p_c(G') <= p_c(G)` and
   `p_u(G') <= p_u(G)`. Consequently:
   - if `p_c(G) < phi(p_u(G))`, then `p_c(G') < p_u(G')`;
   - if `phi^{-1}(p_c(G')) < p_u(G')`, then `p_c(G) < p_u(G)`.

For small `p`, `phi(p)` is about `(p/M)^L`. So a gap transfers only when it has
a margin, roughly `p_c(G) < (p_u(G)/M)^L`. A single added product generator has
`L = 2`, and `M = 2` in the generic case. This does not answer Choi--Seo
Question 1.2.

The proof is in `fpbs-generating-set-threshold-comparison-proof`, with details
in Sections 1--2 of the artifact. No novelty is claimed.
