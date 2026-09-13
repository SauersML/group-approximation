---
rg: 2
id: product-automata-images-contain-fibre-invariant-configurations
kind: claim
title: Over G x K the image of an injective automaton contains every N x 1 invariant configuration when (G/N) x K is surjunctive
distinct_from:
  strict-product-automata-have-no-single-fibre-garden-of-eden: that assumes G surjunctive and K sofic and transplants along sofic models of K; this assumes only that (G/N) x K is surjunctive, nothing about G, and contains that theorem as the case N = G.
  injective-automata-restrict-to-schreier-graph-automata: that is the restriction to the fixed configurations of a subgroup of one group; this applies its normal case to N x 1 inside a product, which settles every Garden of Eden pattern extending to an N x 1 invariant configuration.
artifacts:
  - research/artifacts/quantitative-surjunctivity-residue-2026-09-12.md
---

**ESTABLISHED** by `fibre-invariant-configurations-via-quotient-restriction`.

**Theorem.** Let `N` be normal in `G`, and `tau` an injective automaton on `A^(G x K)` with image `X`. If
`(G/N) x K` is surjunctive, then `X` contains every configuration `x` with `x(ng, k) = x(g, k)` for all `n in N`.

**Cases.**
- **`N = G`, `K` surjunctive.** Every pattern `p` on `E <= G x K` with `p(g,k) = p(g',k)` whenever both sites
  lie in `E` is realized. So every pattern on one fibre `{g} x F` is realized, whatever `G` is. This is the
  conclusion of `strict-product-automata-have-no-single-fibre-garden-of-eden` without its hypothesis on `G`.
- **`K` and `G/N` sofic.** Every pattern extending to an `N x 1` invariant configuration is realized.

**Filter.** Let `p` be a Garden of Eden pattern of a strict automaton over `G x K`, with `K` sofic. For each
normal `N` with `G/N` sofic, `p` takes different values at two sites `(g,k)`, `(g',k)` with `g' g^-1 in N`.

**Consequences.**
- **Single fibres.** The single-fibre filter carries no information about `G`, and it is no progress on
  `products-with-a-sofic-factor-are-surjunctive`.
- **Theorem Q.** The subshift `Y` it builds contains `Fix_N` for every normal `N` with sofic quotient. That is
  exactly the residue left by `quantitative-surjunctivity-constants-lift-from-quotients`.

Proof: Section 1 of the artifact.
