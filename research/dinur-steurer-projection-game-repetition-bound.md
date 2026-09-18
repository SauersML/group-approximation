---
rg: 2
id: dinur-steurer-projection-game-repetition-bound
kind: claim
title: For projection games val(G_1 x ... x G_t)^2 <= prod 2 sqrt(val G_i)/(1+val G_i) (Dinur--Steurer 2014)
distinct_from:
  anchored-quantum-parallel-repetition: that is parallel repetition of anchored games against entangled provers; this is the classical Dinur--Steurer product bound for projection games, which covers unique games.
  dinur-constraint-gap-amplification: that is Dinur's graph-powering gap amplification for constraint graphs; this is parallel repetition of two-prover projection games.
---

**ESTABLISHED, BY CITATION.** Let `G_1, ..., G_t` be projection games, in
particular unique games, each given as a bipartite graph with a (weighted)
edge distribution and one constraint per edge. Let `G_1 x ... x G_t` be their
parallel product: the referee draws one edge of each `G_i` independently,
sends the tuple of left endpoints to Alice and the tuple of right endpoints to
Bob, and accepts iff all `t` constraints hold. Then

```text
val(G_1 x ... x G_t)^2  <=  prod_i  2 sqrt(delta_i) / (1 + delta_i),     delta_i = val(G_i).
```

For a unique game `G` on alphabet `[k]` with edge multiset `E`, the `t`-fold
product `G^(x t)` is again a unique game. Its left side is `U^t`, right side
`V^t`, edge multiset `E^t`, alphabet `[k]^t`, and constraint the coordinatewise
product permutation. Its size is `|E|^t`.

**Consequence used downstream.** `x -> 2 sqrt(x)/(1+x)` is increasing on
`[0,1]`, and `2 sqrt(1-g)/(2-g) <= exp(-g^2/8)` for `0 <= g <= 1`: the
logarithm is `sum_(n>=2) -(g^n/n)(1/2 - 2^-n)`, whose `n = 2` term is `-g^2/8`
and whose other terms are `<= 0`. So `val(G) <= 1 - g` implies

```text
val(G^(x t))  <=  exp(-g^2 t / 16).
```

The inequality is checked on a grid in
`experiments/ugc-sqrt-scale-2026-09-17/output.txt` (check [1]). The same file
checks the product bound against exact values of small random unique games and
their 2-fold products (check [4]).

This is not a new result.

DERIVATION dinur-steurer-projection-game-repetition-citation
