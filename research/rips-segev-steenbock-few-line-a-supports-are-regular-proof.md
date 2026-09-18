---
rg: 2
id: rips-segev-steenbock-few-line-a-supports-are-regular-proof
kind: route
title: In Steenbock's gluing every vertex has one b-edge in and one out and b-runs have length at most 2, so a backtrack-free path of Gamma projects to a non-backtracking walk in the girth-42 graph Phi; the hop lines of a chain of the chain criterion are then pairwise distinct
target: rips-segev-steenbock-few-line-a-supports-are-regular
requires: [rips-segev-sparse-a-support-elements-are-regular]
---

**Conventions.**
- [SP] is `rips-segev-sparse-a-support-elements-are-regular-proof`.  Its §6 has Lemma 6 (the chain lemma) and
  Theorem 2 (the chain criterion).
- [St] is Steenbock, arXiv:1307.0981.  We use its construction of generalized Rips--Segev graphs, the definition
  of `Phi_Gamma`, the Rips--Segev condition, Lemma "mincycle", and section "Explicit constructions".
- The girth of a graph is the least number of edges of a cycle, as in [St].  Loops count as cycles of length 1 and
  pairs of parallel edges as cycles of length 2.
- `N_S = (S - S) \ {0}`.  `gamma = gamma(Gamma)` is the least free product length of a cycle label of `Gamma`.
  `q(gamma) = floor((floor(5 gamma/8) - 3)/2)` is nondecreasing in `gamma`.

## 1. Steenbock's gluing

[St, "Explicit constructions"]: `Phi` is a finite covering of the bouquet of four positively oriented circles
`x_1, ..., x_4`, with vertex degree 8 and `girth(Phi) > 41`.
- Its vertices `1, ..., n` are the `a`-lines of `Gamma`.
- For each vertex `i` there are four edges `x_{ij} = (l_{ij}, i)` into `i` and four edges `y_{ij} = (i, k_{ij})`
  out of `i`, labelled `x_j`.
- An injective `phi : {1..n} -> N` assigns to line `i` the coefficients
  `(I_{i1}, I_{i2}, O_{i1}, O_{i2}, C_i) = (10^{5r-4}, 10^{5r-3}, 10^{5r-2}, 10^{5r-1}, 10^{5r})` with `r = phi(i)`.
- Line `i` is the `a`-path `v_{i,0} -> v_{i,1} -> ... -> v_{i,C_i}`.
- After the `{a,b}`-reduction, the labels are `x_{i1} = b a^{-I_{i1}}`, `x_{i2} = a^{C_l} b a^{-I_{i2}}`,
  `y_{i3} = a^{O_{i1}} b a^{-C_k}` and `y_{i4} = a^{O_{i2}} b`.  Hence every edge `e` of `Phi` carries exactly one
  `b`-edge `E(e)` of `Gamma`, given by the following table.

| edge of `Phi` | `b`-edge of `Gamma` |
|---|---|
| `x_1`: `l -> i` | `v_{l,0} -> v_{i,I_{i1}}` |
| `x_2`: `l -> i` | `v_{l,C_l} -> v_{i,I_{i2}}` |
| `x_3`: `l -> i` | `v_{l,O_{l1}} -> v_{i,C_i}` |
| `x_4`: `l -> i` | `v_{l,O_{l2}} -> v_{i,0}` |

- `E` is a bijection from the edges of `Phi` to the `b`-edges of `Gamma`.
- The distinguished positions of line `i` are `0 < I_{i1} < I_{i2} < O_{i1} < O_{i2} < C_i`.
- The table satisfies the Rips--Segev condition: all differences of distinguished positions, over all lines, are
  nonzero and pairwise distinct.  The script checks this for 1500 rows.
- The least positive element of `Dist_i` is `I_{i1} - 0 = 10^{5r-4}` and the largest is `C_i - 0 = 10^{5r}`.
- By [St, Corollary after Lemma "mincycle"], girth `> 41` gives `Gr'_*(1/8)`, so the results of [SP] apply.

## 2. Structure (Lemma A)

**Lemma A.**  Suppose each line has distinct positions `0 < I_1 < I_2 < O_1 < O_2 < C`.  Then:
- (a) every vertex of `Gamma` is the source of at most one `b`-edge and the target of at most one;
- (b) there is no path of three `b`-edges of one orientation;
- (c) `E(e)` has both endpoints on one line iff `e` is a loop of `Phi`;
- (d) a backtrack-free path never reads `b b^{-1}` or `b^{-1} b`.

*Proof.*
- (a) Each `x_j` is a permutation of the lines.  So each line is the source of exactly one `x_j`-edge and the
  target of exactly one, for each `j`.
  - The sources of the `b`-edges on line `l` are at positions `0, C_l, O_{l1}, O_{l2}`, one for each `j`.
  - The targets on line `i` are at `I_{i1}, I_{i2}, C_i, 0`, one for each `j`.
  - These positions are pairwise distinct within each list, which proves (a).
- (b) Let `u -> v -> w` be two consecutive forward `b`-edges.  Then `v` is both a target and a source, so its
  position is `0` or `C`.
  - The edge leaving position `0` is the `x_1`-edge, which lands at an `I_1` position.
  - The edge leaving position `C` is the `x_2`-edge, which lands at an `I_2` position.
  - An `I` position is never a source, so `w` has no outgoing `b`-edge.
  - Backward runs are the reverse of forward runs.
- (c) `E(e)` for `e : l -> i` has its source on line `l` and its target on line `i`.
- (d) `b b^{-1}` at a vertex `v` means two `b`-edges ending at `v`.  By (a) they are the same edge, so the path
  backtracks.  The case `b^{-1} b` is the same with sources. ∎

So in any backtrack-free path of `Gamma`, the normal form `b`-syllables are exactly the maximal runs of `b`-edges.
Each has 1 or 2 edges, and every `b`-exponent is `±1` or `±2`.

## 3. Projection to Phi (Lemma B) and the girth lemma (Lemma C)

Let `P` be a backtrack-free path of `Gamma` whose consecutive `b`-edges, in order, are `E(e_1), ..., E(e_m)`.
- Between `E(e_t)` and `E(e_{t+1})`, `P` either continues at once, inside a `b`-run, or runs along an
  `a`-segment.
- An `a`-segment of a backtrack-free path is a monotone segment of one line between two distinct positions.
- Either way, `E(e_t)` ends on the line where `E(e_{t+1})` starts, both read in the direction of `P`.
- So `e_1, ..., e_m`, each traversed in the direction `P` uses, form a walk `pi(P)` in `Phi` of length `m`.

**Lemma B.**  If `Phi` has no loops, then `e_{t+1} != e_t` as edges of `Phi` for all `t`.  That is, `pi(P)` is
non-backtracking.

*Proof.*  Suppose `e_{t+1} = e_t = e`, so `E(e)` is used twice in a row.
- *Directly consecutive.*  `E(e)` followed by `E(e)^{-1}` is a backtrack.  `E(e)` followed by `E(e)` in the same
  direction needs the target of `E(e)` to be its source, which is a loop of `Gamma` and so a loop of `Phi`
  (Lemma A(c)).
- *Separated by an `a`-segment* from position `p` to position `p' != p` of line `L`.  `E(e)` arrives on `L` at `p`
  and must leave `L` from `p'`.  So both endpoints of `E(e)` lie on `L`, and `e` is a loop by Lemma A(c).
- Both cases are excluded. ∎

**Lemma C.**  In a graph of girth `g`, a non-backtracking walk `w_0, f_1, w_1, ..., f_m, w_m` with `m < g` has
pairwise distinct vertices `w_0, ..., w_m`.

*Proof.*  Take `s < t` with `w_s = w_t` and `t - s` minimal.  Then `w_s, ..., w_{t-1}` are distinct.
- If `t - s = 1`, then `f_t` is a loop.
- If `t - s = 2`, then `f_{s+1} != f_{s+2}` are parallel edges.
- If `t - s >= 3`, the subwalk is a simple cycle.
- Each case is a cycle of length `t - s <= m < g`, a contradiction. ∎

**Corollary (gamma >= g).**  If `Phi` has girth `g` and no loops, then `gamma(Gamma) >= g`.
- Let `c` be a cycle of `Gamma`, that is a closed backtrack-free path traversed cyclically.
- `c` contains a `b`-edge, since the lines are paths and not cycles.
- `c` is not one `b`-run, by Lemma A(b), since `b`-runs have `<= 2 < 3` edges.
- So its cyclic label is `a^{n_1} b^{e_1} ... a^{n_L} b^{e_L}`.  All exponents are nonzero, the `b`-syllables are
  the maximal `b`-runs, and `|e_k| <= 2`.
- Lemma B applied cyclically makes `pi(c)` a closed non-backtracking walk of length `m = sum |e_k| <= 2L`.
- By Lemma C, `m >= g`.  So `|label|_* = 2L >= m >= g`.

This agrees with [St, Lemma "mincycle"].  For Steenbock's graphs, `gamma >= g >= 42`, and `q(gamma) >= q(42) = 11`.

**The two facts asked for in [SP] §6.**
- `gamma >= 42 >= 12`.
- A `b`-edge `v_{1,0} -> v_{1,10}` would have its source at position 0.  So it would be `E(e)` for an `x_1`-edge
  `e : 1 -> i` with `I_{i1} = 10`, that is `phi(i) = 1`.  Since `phi` is injective and line 1 has row 1, `i = 1`.
  Then `e` is a loop, and `Phi` has none.
- So [SP] §6 "Example" is now a proof: every `u(a) + w(a) b` of joint `a`-span `<= 89` is a non-zero-divisor.
  §4 below subsumes this.

## 4. The few-line criterion

For a line `i`, `Dist_i` is the set of differences of two distinct distinguished positions of `i`.  Put
`L_S = {i : N_S ∩ Dist_i != ∅}`.

**Theorem.**  Suppose `Gamma` has Steenbock's gluing pattern (§1, with any coefficients
`0 < I_1 < I_2 < O_1 < O_2 < C` per line) and satisfies `Gr'_*(1/8)`.  Suppose `Phi` has girth `g` and no loops.
Put `q = q(g)`.  Let `beta = sum_{i in S, j in J} c_ij a^i b^j != 0` with `S, J` finite.  If `|L_S| < q`, then
`beta` is a non-zero-divisor in `k[K]` and in `k[G(Gamma)]`.

*Proof.*
- Suppose not.  By [SP] Theorem 2, `Gamma` has an `(N_S, N_J)`-chain of length `q(gamma)`.
- Since `gamma >= g` (§3) and `q` is nondecreasing, `q(gamma) >= q`.
- An initial piece of a backtrack-free path is backtrack-free.  So there is a backtrack-free path `P` with label
  `b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}`, all `n_k in N_S`.  (If `q <= 0` the hypothesis `|L_S| < q` is
  empty.)
- *Hop lines.*  The syllable `a^{n_k}` is a monotone segment of one line `l_k`.  Its two ends carry the adjacent
  `b`-edges, so they are distinguished positions of `l_k`.  Hence `n_k in N_S ∩ Dist_{l_k}` and `l_k in L_S`.
- *The walk.*  Let `P'` be the subpath of `P` from the start of `a^{n_1}` to the end of `a^{n_q}`.
  - `P'` is backtrack-free, and its `b`-edges are those of `b^{e_1}, ..., b^{e_{q-1}}`.
  - By Lemma A these number `m = sum_{k=1}^{q-1} |e_k| <= 2(q - 1)`.
  - By Lemma B, `pi(P')` is a non-backtracking walk of length `m` in `Phi`.  It starts at `l_1`, ends at `l_q`,
    and passes through `l_k` after `|e_1| + ... + |e_{k-1}|` steps.
  - These `q` step counts are strictly increasing, since every `|e_k| >= 1`.
- *Girth.*  `m <= 2(q - 1) <= floor(5g/8) - 5 < g`.  By Lemma C the vertices of `pi(P')` are pairwise distinct,
  so `l_1, ..., l_q` are `q` distinct elements of `L_S`.
- This contradicts `|L_S| < q`. ∎

**Mirror forms and translates.**
- Let `*` be the `k`-linear anti-automorphism `g -> g^{-1}`.  For `beta' = sum c_ij b^j a^i`,
  `beta'^* = sum c_ij a^{-i} b^{-j}` is supported on `a^{-S} <b>`, and `N_{-S} = N_S`.
- `*` exchanges left and right zero divisors.  So `beta'` is regular iff `beta'^*` is.
- Multiplying by units preserves regularity, which gives the translates `x beta y`.

**Corollary (Steenbock's graphs).**  `g >= 42`, so `q >= q(42) = 11`.
- If `max S - min S < 10^{51}`, then `N_S ⊂ (-10^{51}, 10^{51})`.
- The least positive element of `Dist_i` is `10^{5 phi(i) - 4}`.  So `i in L_S` forces `phi(i) <= 10`.
- `phi` is injective, so `|L_S| <= 10 < 11`.
- Hence every nonzero element of `k[K]` supported on `a^S <b>` or `<b> a^S` with `a`-span `< 10^{51}` is a
  non-zero-divisor in `k[K]` and `k[G(Gamma)]`.  This holds for every field `k`, every finite `J` and all
  coefficients.
- Two special cases:
  - `J = {0, 1}` and `S ⊆ [0, 89]` is the [SP] §6 example, including `1 + a^{10} + b`.
  - `J = {0}` is `u(a)`, which is regular in any case.
- More generally, the conclusion holds whenever `N_S` meets the `Dist` sets of at most 10 lines, whatever the span.
  - Example: `S = {0, 10, 10^{60}}`.  Here `N_S = ±{10, 10^{60} - 10, 10^{60}}`.  The values `10 = I_1` (row 1) and
    `10^{60} = C` (row 12) lie in `Dist`.  The value `10^{60} - 10` does not, since it mixes rows.  So `|L_S| = 2`.
  - Hence `1 + a^{10} + a^{10^{60}} b` is regular.  It is covered neither by the sparse node, since `10 in Dist`,
    nor by the span bound.

**Sharpness of the method.**
- The girth enters only through Lemma C, applied to walks of length `<= 2(q - 1)`.
- For contiguous `S` of span `>= max_i C_i`, every line lies in `L_S`.  Every relator label is then an
  `(N_S, N_J)`-chain of arbitrary length, and the criterion says nothing.
- Such elements need an argument that uses the coefficients.  The alternating walk of [SP] §4 must be followed with
  the actual cancellation pattern of `alpha beta = 0`, not only with its support.

## 5. Computation

`experiments/rips-segev-few-line-2026-09-18/steenbock_chains.py` (output in `results.txt`, seeds 1--3) works as
follows.
- It builds the gluing of §1 for `n = 1500` lines, with random permutations `sigma_1, ..., sigma_4`.
- It removes short cycles by random swaps until `girth(Phi) >= 5`.  The paper's girth 42 is out of reach at this
  size, which is why walk lengths are compared with the actual girth.
- It asserts Lemma A(a), A(b), A(c) (same-line `b`-edges = loops of `Phi` = 0) and the Rips--Segev condition.
- For `M in {89, 10^6, 10^{11}, 10^{16}, 10^{26}, 10^{36}}`, it enumerates every chain with `<= 6` hops of length
  `<= M` from lines in `L_S`.
  - It asserts that every chain whose projected walk is shorter than the girth has pairwise distinct hop lines,
    all in `L_S`.
  - There are 0 violations in all 12 configurations.
- With random rows the longest chain has 1 hop.
- With rows clustered on a BFS ball of `Phi`, chains of 3 hops occur.  Here `L_S` induces a star, whose paths have
  at most 3 vertices.  No line repeats.
- *Control.*  Swapping `sigma_1` so that it fixes the row-1 line creates the loop, and the edge
  `v_{1,0} -> v_{1,10}` appears.  Chains of up to 6 hops repeating line 1, with projected walk length 1, then exist.
  This is exactly the failure that Lemma B excludes.
