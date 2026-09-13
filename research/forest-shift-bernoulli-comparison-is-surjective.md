---
rg: 2
id: forest-shift-bernoulli-comparison-is-surjective
kind: claim
title: Over a torsion-free host the forest-shift Bernoulli comparison is surjective, equivalently Baum--Connes surjectivity holds at the forest coefficient C_0(T minus 0)
distinct_from:
  bernoulli-cylinder-comparison-fails-for-some-group: that asks for a surjectivity failure of the full-shift comparison; this asks for surjectivity of the comparison restricted to configurations whose support induces a forest.
---

**OPEN.** Let `G` be torsion-free with finite symmetric generating set `S`, and let
`T = {x ∈ (Z/p)^G : supp x induces a forest in Cay(G, S)}`. The claim is that the forest comparison
`T_r^T : ⊕_([s] forest pattern) Z -> K_0(C_0(T \ {0}) ⋊_r G)`, `[s] ↦ [1_(C_s ∩ T)]`, is surjective and that
`K_1(C_0(T \ {0}) ⋊_r G) = 0`.

By weak K-equivalence and going-down this is Baum--Connes surjectivity for `G` with coefficients `C_0(T \ {0})`
(`research/artifacts/bc-bernoulli-hls-ghost-lift-2026-09-13.md`, Lemma 2.1).

**What it would give.** Take a host satisfying (M) and (H-K) of `hls-ghost-lift-needs-forest-shift-failure`. For that
host no full-shift class carries ghost ranks on the marked expanders with vanishing tree-boundary part. So the HLS class
does not lift, and `hls-ghost-class-lifts-to-the-bernoulli-full-shift` fails for that host.

## Attempts

- **Free groups.** If `Cay(G, S)` is a tree, then `T` is the full shift and `G` is free. It satisfies Baum--Connes with
  coefficients, so the comparison is an isomorphism (CEKN Theorem 2.8).
- **Finite strata and locality.**
  - The strata of fixed support size are proper and their crossed products are exact (CC Lemma E), so the truncations of
    RF Lemma R6 go through on `T`.
  - The mixed-difference argument of `bernoulli-pattern-expansions-are-finite` uses only removals, so it applies on `T`.
    Hence shape (a) is empty on `T`.
- **Where it stops.**
  - What remains are rank-invisible forest classes in `∩_k im K_0(I_k(T) ⋊_r G)`, and `K_1`.
  - `T ⋊ G` is not a-T-menable when `G` does not coarsely embed: configurations with two far-apart components realize the
    pair groupoid of `G`. So Tu's theorem does not apply directly.
  - The infinite forest configurations are tree-like, but they accumulate on the proper strata, and the `lim^1`
    phenomenon lives there.
