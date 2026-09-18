---
rg: 2
id: rips-segev-steenbock-few-line-a-supports-are-regular
kind: claim
title: In Steenbock's explicit Rips--Segev core every element of k[a^S <b>] of a-span below 10^51 is a non-zero-divisor, for any number of b-layers, because chain hops sit on pairwise distinct lines of the girth-42 graph Phi
distinct_from:
  rips-segev-sparse-a-support-elements-are-regular: that needs (S - S) to miss Dist(Gamma) entirely (no chain of length 1); this allows S - S to meet the Dist sets of up to q(g) - 1 lines (10 lines for Steenbock's graphs), so for example 1 + a^10 + b and every contiguous S of span below 10^51 are covered.
  rips-segev-short-syllable-two-layer-elements-are-regular: that treats two layers of contiguous reduced span below m_Gamma = 10; this treats any number of layers and a-span up to 10^51 - 1 in Steenbock's graphs.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all elements of k[G(Gamma)]; this settles it for every element supported on a^S <b> (or <b> a^S) with |L_S| < q(girth Phi).
artifacts:
  - experiments/rips-segev-few-line-2026-09-18/steenbock_chains.py
  - experiments/rips-segev-few-line-2026-09-18/results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-steenbock-few-line-a-supports-are-regular-proof`.

**Setting.**
- `K = (<a> * <b>) / <<R>>` is the core of Steenbock's explicit generalized Rips--Segev graph `Gamma`
  (arXiv:1307.0981, section "Explicit constructions").  `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2` with `G_1 ∋ a`,
  `G_2 ∋ b` torsion-free.
- Steenbock's gluing, reconstructed from the paper:
  - `Phi` is a finite 8-regular covering of the bouquet of four circles `x_1, ..., x_4`, of girth `g > 41`.
    Its vertices are the `a`-lines of `Gamma`.
  - Line `i` uses row `phi(i)` of the table `(I_1, I_2, O_1, O_2, C) = (10^{5r-4}, ..., 10^{5r})`, with `phi`
    injective.  Its distinguished positions are `0, I_1, I_2, O_1, O_2, C`.
  - The `b`-edges are in bijection with the edges of `Phi`.  An `x_j`-edge `l -> i` of `Phi` gives
    `v_{l,0} -> v_{i,I_{i1}}` (j = 1), `v_{l,C_l} -> v_{i,I_{i2}}` (j = 2), `v_{l,O_{l1}} -> v_{i,C_i}` (j = 3), or
    `v_{l,O_{l2}} -> v_{i,0}` (j = 4).
- `N_S = (S - S) \ {0}`.  `Dist_i` is the set of differences of two distinct distinguished positions of line `i`.
  `L_S` is the set of lines `i` with `N_S ∩ Dist_i != ∅`.
- `q(gamma) = floor((floor(5 gamma / 8) - 3) / 2)` is the chain length of Theorem 2 of
  `rips-segev-sparse-a-support-elements-are-regular-proof`.  `q(42) = 11`.

**The two facts asked for by the sparse node both hold.**
- `gamma(Gamma) >= g >= 42 >= 12`.  This is Steenbock's Lemma "mincycle".  The proof file also gives a
  self-contained proof from the gluing.
- There is no `b`-edge `v_{1,0} -> v_{1,10}`.  Such an edge would be an `x_1`-loop of `Phi` at the row-1 line, and
  `Phi` has no loops since `g > 1`.  More generally, no `b`-edge joins two vertices of one line.

So the sparse node's reduction closes: every `u(a) + w(a) b` of joint `a`-span `<= 89` is regular, including
`1 + a^{10} + b` and `(1 + a)^{10} + b`.  The theorem below is much stronger.

**Theorem (few-line criterion).**  Let `Gamma` be Steenbock's graph, or any generalized Rips--Segev graph with
Steenbock's gluing pattern (positions `0 < I_1 < I_2 < O_1 < O_2 < C` on each line) that satisfies `Gr'_*(1/8)`,
and let `g` be the girth of its `Phi`.  Let `k` be a field, let `S, J ⊂ Z` be finite, and let
`beta = sum_{i in S, j in J} c_ij a^i b^j != 0`.  If `|L_S| < q(g)`, then `beta` is a non-zero-divisor in `k[K]`
and in `k[G(Gamma)]`.  The same holds for `sum c_ij b^j a^i` and for every translate `x beta y`.

**Corollary (Steenbock's graphs, `g >= 42`).**
- The least element of `Dist_i` on row `r` is `10^{5r-4}`.  If `max S - min S < 10^{51}`, only lines of rows
  `r <= 10` lie in `L_S`, so `|L_S| <= 10 < 11 = q(42)`.
- Hence every element of `k[K]` supported on `a^S <b>` with `a`-span `< 10^{51}` is a non-zero-divisor.  This
  holds with any number of `b`-layers, any `b`-exponents and any coefficients.  Examples are
  `(1 + a)^{10^{50}} + b + b^{-3}` and `1 + a^{10} + b`.
- For a general girth `g` the bound is `a`-span `< 10^{5 q(g) - 4}`.
- Large span with few lines also works.  For `S = {0, 10, 10^{60}}`, `|L_S| = 2` (rows 1 and 12), so
  `1 + a^{10} + a^{10^{60}} b` is regular.  This element is covered by neither the sparse node nor the span bound.

**Mechanism.**
1. *Structure.*  Every vertex of `Gamma` has at most one outgoing and one incoming `b`-edge.  A run of `b`-edges of
   one orientation has at most 2 edges.  A `b`-edge inside one line is a loop of `Phi`.
2. *Projection.*  Reading off the `b`-edges of a backtrack-free path of `Gamma` gives a walk in `Phi` with no
   immediate reversal.
3. *Girth.*  A non-backtracking walk of length `< g` visits pairwise distinct vertices.
4. *Chains.*  The chain criterion gives a chain of `q(g)` hops if `beta` is a zero divisor.  Hop `k` lies on a line
   `l_k in L_S`, and consecutive hops are joined by `<= 2` `b`-edges.  So `l_1, ..., l_q` lie on a
   non-backtracking walk of length `<= 2(q - 1) < g`.  They are therefore distinct, and `|L_S| >= q`.

**Calibration.**
- `|L_S| = 0` is Theorem 1 of the sparse node.
- For contiguous `S` of span above `max_i C_i`, every relator label is a chain.  Here `L_S` is every line and the
  theorem is silent, as it must be.
- `experiments/rips-segev-few-line-2026-09-18/steenbock_chains.py` builds the gluing on 1500 lines with girth-5
  `Phi`.  It checks structural facts (1)--(3) and the Rips--Segev distance condition.
- It then enumerates every chain with hops `<= M`, for `M` up to `10^{36}`.  All chains of walk length `< girth`
  have distinct hop lines in `L_S` (0 violations over 3 seeds).
- With rows clustered on a ball of `Phi`, chains of 3 hops occur, which is still `<= |L_S|`.
- Control: planting a loop at the row-1 line creates the edge `v_{1,0} -> v_{1,10}`, and 6-hop chains repeating
  line 1 appear.  So the girth hypothesis is used.

**Not covered.**  Elements with `|L_S| >= 11`, for example contiguous `S` of span `>= 10^{51}`.  There, chains
through `>= 11` distinct lines exist, and the coefficients along the alternating walk must enter.
