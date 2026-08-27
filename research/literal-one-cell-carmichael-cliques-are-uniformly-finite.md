---
rg: 2
id: literal-one-cell-carmichael-cliques-are-uniformly-finite
kind: claim
title: A fixed free-word edge template cannot support unbounded Carmichael cliques
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that permits a uniformly bounded-area interaction of several presentation cells; this rules out the stronger attempt in which every pair word is one literal conjugate of a fixed finite template list.
  literal-orbital-graph-block-clique: that proves completeness of blocks in an affine lamp-kernel orbital graph after passing to the quotient group; this is a free-word obstruction to coherent names in the Bleak--Quick presentation.
  finite-normalizer-star-no-go: that bounds predicate capacity of a fixed finite packet normalizer; this uses proper tree geometry of a free group before imposing any relators.
---

Let `F=F(X)` be a finite-rank free group and let `b in X` be a free
generator.  For every `L` there is `K=K(F,L)` such that the following holds.
If `S` is a set of distinct conjugates of `b` and

```text
cyc_len((uv)^2) <= L                  for all distinct u,v in S, (LOC1)
```

then `|S|<=K`.

Consequently, fix any finite list `Q` of free words.  There is no arbitrarily
large family of global words `u_i=g_i^(-1)b g_i` for which every Carmichael
edge word `(u_i u_j)^2` is freely equal to a conjugate of an element of `Q`.
In particular a coherent Thompson Carmichael compiler cannot assign every
edge a single literal conjugate of one fixed R1--R5 consequence.  It must use
genuinely interacting bounded-area cells, or a weaker averaged
synchronization mechanism.
