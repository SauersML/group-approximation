---
rg: 2
id: fpbs-generating-set-threshold-comparison-proof
kind: route
title: Give each new edge private randomness along a fixed word path and compare two-point functions
target: fpbs-generating-set-threshold-comparison
requires:
  - fpbs-hp-uniqueness-and-long-range-order
  - fpbs-cluster-count-trichotomy
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

**The coupling.**
- **Randomness.** Take independent uniforms: one per *use*, meaning one per
  (edge of `G'`, path of that edge, step), and one padding uniform per edge of
  `G`.
- **The configuration `xi` on `G'`.** Put `b = phi(p)` and
  `c = 1 - (1-p)^{1/M}`. An edge of `G'` is open in `xi` iff all uniforms along
  one of its paths are below the path threshold. For a path of length `l` the
  threshold is `beta^{1/l}`, with `beta = b` for one path and `beta = 1 - sqrt(1-b)`
  for the two paths of an involution.
  - `xi` is Bernoulli(`b`) on `G'`, since distinct edges use disjoint uniforms.
  - Every use threshold is at most `c`.
- **The configuration `omega` on `G`.** An edge of `G` is open in `omega` iff
  one of its uses fires, or its padding uniform lies below `z_e`. Here `z_e` is
  chosen so that the probability is exactly `p`; this is possible because
  `prod (1 - c_j) >= (1-c)^M = 1-p`. So `omega` is Bernoulli(`p`) on `G`.
- **Clusters nest.** An open `xi`-edge has an `omega`-open path between its
  endpoints. So every `xi`-cluster lies inside one `omega`-cluster, which gives
  the pointwise inequalities for `tau`, `theta` and `chi^I`.

**`p_u(G') >= phi(p_u(G))`.**
- For `p < p_u(G)`, `G_p` has no unique infinite cluster, because `p_u` is an
  infimum.
- `fpbs-hp-uniqueness-and-long-range-order` with `H = Gamma` gives
  `inf tau^G_p = 0`.
- By the comparison, `inf tau^{G'}_{phi(p)} = 0`. The same import shows
  `G'_{phi(p)}` has no unique infinite cluster.
- By `fpbs-cluster-count-trichotomy`, every `q > p_u(G')` has one, so
  `phi(p) <= p_u(G')`.
- Let `p` increase to `p_u(G)` and use continuity of `phi`.

**`p_c(G') >= phi(p_c(G))`.**
- If `phi(p) > p_c(G')`, then `theta^{G'}(phi(p)) > 0`, hence `theta^G(p) > 0`,
  hence `p >= p_c(G)`.
- The relative threshold inequality follows the same way, since an
  `I`-infinite `xi`-cluster lies inside an `omega`-cluster containing the same
  vertices of `I`.

**Nested sets.**
- If `S ⊆ S'`, restricting a Bernoulli configuration on `G'` to the edges of `G`
  gives `tau^G_q <= tau^{G'}_q` and `theta^G(q) <= theta^{G'}(q)`. So
  `p_c(G') <= p_c(G)`.
- For `q > p_u(G)`:
  - `G_q` is unique, so `inf tau^G_q > 0` by the import;
  - hence `inf tau^{G'}_q > 0`;
  - hence `G'_q` is unique by the import, and `q >= p_u(G')`.
- The two gap transfers are the chains
  - `p_c(G') <= p_c(G) < phi(p_u(G)) <= p_u(G')`;
  - `p_c(G) <= phi^{-1}(p_c(G')) < p_u(G') <= p_u(G)`.
