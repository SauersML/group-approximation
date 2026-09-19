---
rg: 2
id: raz-rosen-expander-parallel-repetition-bound
kind: claim
title: On a biregular bipartite question graph with normalized spectral gap lambda, a game of value 1-eps (eps < 1/2) has n-fold value at most (1 - eps^2 c(lambda))^(n/log s) with c(lambda) = 10^-12 lambda^2/(32 log^2(2/lambda)), and a projection game at most (1 - eps poly(lambda))^n, the proof instantiating poly(lambda) as Theta(lambda^4/log(2/lambda)) (Raz--Rosen 2012, Theorems 1 and 2)
distinct_from:
  akkstv-expansion-parallel-repetition-bound: that is the AKKSTV unique-games bound with rate eps lambda/log(1/eps), proved through the Feige--Lovasz SDP; this is the information-theoretic Raz--Rosen bound for general and projection games, with rates eps^2 lambda^2/log^2(2/lambda) and eps lambda^4/log(2/lambda).
  dinur-steurer-projection-game-repetition-bound: that is a universal quadratic bound for projection games independent of expansion; this is linear in eps for projection games at the price of a poly(lambda) factor.
  raz-odd-cycle-repetition-lower-bound: that is a lower bound on repeated values of a non-expanding game; this is an upper bound on expanding question graphs.
---

**ESTABLISHED, BY CITATION.** R. Raz and R. Rosen, *A Strong Parallel
Repetition Theorem for Projection Games on Expanders*, CCC 2012 (ECCC TR10-142).
Verbatim text and the reading used here are in
`raz-rosen-expander-parallel-repetition-citation`.

*Form used in this graph.* Let `G` be a two-prover game whose question
distribution is uniform on the edges of a biregular bipartite graph with
normalized biadjacency `M`, and let `1 − λ` be the second largest singular value
of `M` (so `λ in [0, 1]`, and `G` is λ-gapped in the sense of
`expansion-certified-repetition-caps-deficit-ratio`). Let `val(G) = 1 − ε`
with `ε < 1/2` and answer set size `s >= 2`.

1. *(General games, Theorem 1.)* `val(G^(⊗n)) <= (1 − ε^2 c(λ))^(n/log s)`,
   `c(λ) = (1/32)·10^(−12)·λ^2/(log(2/λ))^2`.
2. *(Projection games, Theorem 2 as proved.)* There is an absolute constant
   `c_P in (0, 1]` such that
   `val(G^(⊗n)) <= (1 − c_P·ε·λ^4/log(2/λ))^n` for all `n >= 1`.
   The constant is `c_P = c·10^(−40)` with `c` Rao's constant; the derivation
   from the quoted proof is item 3 of the route's reading.
