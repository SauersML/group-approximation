---
rg: 2
id: steurer-parallel-repeated-unique-games-rounding
kind: claim
title: If the basic SDP value of a unique game G with alphabet size k is at least 1-eps then its l-fold parallel repetition has value at least 1 - O(sqrt(l eps log k)), with the constant absolute and independent of l, and opt(G^l) <= sdp(G)^l (Steurer, APPROX-RANDOM 2010, Theorems 1 and 7; Barak--Hardt--Haviv--Rao--Regev--Steurer FOCS 2008 up to a log(1/eps) factor)
distinct_from:
  cmm-unique-games-sqrt-log-k-rounding: that rounds the basic SDP of an arbitrary unique game, with the log of its own alphabet; applied to G^l it pays log(k^l) = l log k. This bound pays only the base log k, so rounds are not charged against the alphabet.
  raz-odd-cycle-repetition-lower-bound: that is the lower bound on repeated values of one family (odd cycles); this is the general lower bound on every unique game in terms of its SDP value, of which the odd-cycle bound is the tight instance at k = 2.
  akkstv-expansion-parallel-repetition-bound: that is an upper bound on repeated values from expansion; this is a lower bound valid on every game.
  dinur-steurer-projection-game-repetition-bound: that is a universal upper bound on repeated values of projection games; this is a lower bound specific to unique games.
---

**ESTABLISHED, BY CITATION.** Source: D. Steurer, *Improved Rounding for
Parallel Repeated Unique Games*, APPROX-RANDOM 2010 (LNCS 6302). It improves
B. Barak, M. Hardt, I. Haviv, A. Rao, O. Regev and D. Steurer, *Rounding
Parallel Repetitions of Unique Games*, FOCS 2008, which has the weaker factor
`s = log k + log(1/eps)`. The verbatim text and its reading are in the route.

*Form used in this graph.* Let `sdp(G)` be the basic unique-games SDP value:

```text
sdp(G) = max E_{(u,v,pi)~G} sum_i <u_i, v_pi(i)>,
          subject to sum_i ||u_i||^2 = 1 and <u_i, u_j> = 0 (i != j) at every vertex.
```

This is the same program that `spectral-gap-no-output-kill-proof` solves by
`sdp-fixed-precision-solvable-gls`. There is an absolute constant `C_1 >= 1`
such that, for every unique game `G` with alphabet size `k >= 2` and every
integer `l >= 1`, the following hold.

- **(S1), Theorem 1.** `sdp(G) >= 1 - eps` implies
  `opt(G^l) >= 1 - C_1 sqrt(l eps ln k)`.
- **(S2), Theorem 7 (Feige--Lovász), as restated by Steurer.**
  `sdp(G^l) = sdp(G)^l`, and hence `opt(G^l) <= sdp(G)^l`.

Here `G^l` is the `l`-fold parallel repetition. It has vertex set `V^l`,
alphabet `Sigma^l`, and coordinatewise permutations on `l`-tuples of
independent constraints.

Credit is the authors'. Nothing is reproved here.

**Tightness (quoted).** The abstract gives the amortised form
`sdp(G)^{O(log k)} <= sup_l opt(G^l)^{1/l} <= sdp(G)`. The paper states that
"for every k ∈ ℕ, there exist unique games G that achieve the above lower bound
on opt(G)". At `k = 2` the odd-cycle game is the tight instance (see
`raz-odd-cycle-repetition-lower-bound`).

DERIVATION steurer-parallel-repeated-unique-games-rounding-citation
