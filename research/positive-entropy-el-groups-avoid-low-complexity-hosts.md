---
rg: 2
id: positive-entropy-el-groups-avoid-low-complexity-hosts
kind: claim
title: If G_X embeds in G_Y for infinite minimal subshifts then p_X(k) ≤ 7·p_Y(Ck²)^4; so positive-entropy G_X is a subgroup of no G_Y with log p_Y(n) = o(√n)
distinct_from:
  subshift-elementary-group-lef-growth-complexity-bounds: that proves the upper and lower LEF growth bounds and a non-isomorphism consequence; this derives an obstruction to injective homomorphisms G_X → G_Y from those bounds through subgroup monotonicity of LEF growth
  lef-growth-of-subshift-el-groups-is-monotone-under-factors: that shows G_Y ≤ G_X when Y is a factor of X, with growth monotone along factors; this is the reverse obstruction, a complexity inequality forced by any embedding
artifacts:
  - research/artifacts/sk-free-7-non-embeddability-2026-09-13.md
---

**ESTABLISHED (unreviewed)**, conditional only on `subshift-elementary-group-lef-growth-complexity-bounds` (unreviewed).

Let X, Y ⊆ A^Z be infinite minimal subshifts. Put G_X = EL_3(LC(X,F_2) ⋊ Z), and let p_X be the complexity function.

**Theorem.** If G_X is isomorphic to a subgroup of G_Y, there is a constant C such that, for all large k,

`p_X(k) ≤ 7 · p_Y(C k^2)^4`.

**Corollaries.**
- **Entropy.** If X has positive topological entropy and log p_Y(n) = o(√n), then G_X is not isomorphic to a subgroup of G_Y. This applies to every Y of polynomial complexity: Sturmian, linearly recurrent and primitive substitutive subshifts.
- **Polynomial scales.** If p_X(k) ≥ c k^α for infinitely many k and p_Y(n) ≤ C′ n^β for all n, with α > 8β, then G_X is not isomorphic to a subgroup of G_Y.
- **Strict inclusions.** When Y is a factor of X, G_Y ≤ G_X (`lef-growth-of-subshift-el-groups-is-monotone-under-factors`). If moreover X has positive entropy and Y polynomial complexity, the reverse embedding fails.

The derivation is route `positive-entropy-el-groups-avoid-low-complexity-hosts-proof`.

**Review (sk-verify-15, 2026-09-13): PASS, conditional.** Subgroup monotonicity L_X(r) ≤ L_Y(Cr), N_Y ≤ 2p_Y², the arithmetic at r = 500k² and all three corollaries re-derived. Conditional on both bounds of `subshift-elementary-group-lef-growth-complexity-bounds`, which is unreviewed and not re-derived here. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §1.
