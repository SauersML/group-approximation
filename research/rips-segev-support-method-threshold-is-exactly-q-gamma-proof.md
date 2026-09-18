---
rg: 2
id: rips-segev-support-method-threshold-is-exactly-q-gamma-proof
kind: route
title: A repeated hop line closes the intervening chain segment into a cycle of free-product length at most 2(q - 1) < gamma, so the q(gamma) hop lines of a chain are distinct and |L_S| < q(gamma) gives regularity; a Cayley graph of a finite quotient of <x | (x_4 x_1)^21> realizes gamma = 42
target: rips-segev-support-method-threshold-is-exactly-q-gamma
requires: [rips-segev-sparse-a-support-elements-are-regular, rips-segev-steenbock-eleven-point-a-supports-are-regular]
---

**Conventions.**
- [FL] is `rips-segev-steenbock-few-line-a-supports-are-regular` with its proof file.
- [SP] is `rips-segev-sparse-a-support-elements-are-regular-proof`.
- [EP] is `rips-segev-steenbock-eleven-point-a-supports-are-regular-proof`.

Notation is that of [FL].  A *cycle* of `Gamma` is a closed backtrack-free path traversed cyclically.  `gamma` is
the least free-product length `|.|_*` of a cycle label.  Lines are paths (not cycles), and all `a`-edges of
`Gamma` lie on lines.  Lemma A of [FL] says the graph is reduced: each vertex has at most one `b`-edge in and at
most one out.

## 1. Hop lines are distinct

**Lemma 1.**  Let `P` be backtrack-free with label `b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}`, all exponents
nonzero, the `b`-syllables maximal `b`-runs.  Let `l_k` be the line carrying `a^{n_k}`.  If `2(q - 1) < gamma`,
then `l_1, ..., l_q` are pairwise distinct.

*Proof.*  Suppose `l_s = l_t = l` with `s < t`.
- Let `x` be the end of `a^{n_s}` and `y` the start of `a^{n_t}`.  Both are vertices of `l`.
- Let `R` be the subpath of `P` from `x` to `y`.  It is backtrack-free, with label
  `b^{e_s} a^{n_{s+1}} ... a^{n_{t-1}} b^{e_{t-1}}`.  That label has `2(t - s) - 1` syllables.

*Case `x != y`.*
- Let `sigma` be the monotone segment of `l` from `y` to `x`.  It is nonempty.
- The closed path `R sigma` is backtrack-free, cyclically as well.  At `y` a `b`-edge meets an `a`-edge, and so
  does `sigma` at `x`.
- Its cyclic label alternates `t - s` nonzero `b`-syllables with `t - s` nonzero `a`-syllables.  So it is a cycle
  of free-product length exactly `2(t - s)`.

*Case `x = y`.*
- `R` is a nonempty backtrack-free closed path.  Cyclically reduce it by deleting a final edge that is the
  inverse of the initial edge, as often as possible.
- The result `R_0` is nonempty.  In a graph, a backtrack-free closed path is a nontrivial element of `pi_1`,
  and cyclic reduction replaces it by a conjugate.
- `R_0` is a cycle.  Its label is obtained from that of `R` by deleting letters at the two ends, so its cyclic
  free-product length is at most the linear free-product length of `R`, which is `2(t - s) - 1`.

If `gamma` is instead defined through simple cycles, take a simple cycle inside the closed path above.  Its cyclic
label is a subword of the linear label read from `x`, which has at most `2(t - s)` syllables.

Either way `gamma <= 2(t - s) <= 2(q - 1) < gamma`, a contradiction. ∎

Nothing here uses `Phi`: Lemmas B and C of [FL], the girth and looplessness are not needed.

**Arithmetic.**  With `F = floor(5 gamma / 8)`, `q(gamma) = floor((F - 3)/2)` gives
`2 q(gamma) <= F - 3`.  So `2(q(gamma) - 1) <= F - 5 < gamma`.

## 2. Regularity

**Theorem.**  If `|L_S| < q(gamma)`, then every nonzero `beta = sum_{i in S, j in J} c_ij a^i b^j` is a
non-zero-divisor in `k[K]` and `k[G(Gamma)]`.

*Proof.*
- If not, [SP] Theorem 2 gives an `(N_S, N_J)`-chain of length `q = q(gamma)`: a backtrack-free path with label
  `b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}` and all `n_k in N_S`.
- As in [FL] §4 ("hop lines"), the ends of `a^{n_k}` carry `b`-edges, so they are distinguished positions of
  `l_k`.  Hence `n_k in Dist_{l_k} ∩ N_S` and `l_k in L_S`.
- By Lemma 1 and the arithmetic, the `l_k` are `q` distinct elements of `L_S`.  This is a contradiction. ∎

The mirror form `sum c_ij b^j a^i` and translates follow as in [FL] §4, using `*` and units.  For Steenbock's
table, [EP] Lemma 1 (super-increasing rows) gives `|L_S| <= |S| - 1`.  So `|S| <= q(gamma)` suffices.

**Threshold.**
- [EP] ("limit of the support method") reads `q(gamma)` consecutive hops off a shortest cycle and puts
  `S = {0, n_1, n_1 + n_2, ...}`, `J = {0, 1, 2}`.  Then `|S| = q(gamma) + 1`, and the segment is an
  `(N_S, N_J)`-chain of length `q(gamma)`.
- So [SP] Theorem 2's hypothesis fails there.  The chain criterion is decisive for all `|S| <= q(gamma)` and silent
  at some `S` of size `q(gamma) + 1`.

## 3. How gamma depends on Phi

Lift a walk of `Phi` to `Gamma` edge by edge.
- Arriving by `E(e_t)` at position `p` of line `i`, and leaving by `E(e_{t+1})` from position `p'`, the lift runs
  `a^{p' - p}` on `i`.
- From the gluing table:
  - arrivals: forward `x_1, x_2, x_3, x_4` arrive at `I_1, I_2, C, 0`, and backward ones at `0, C, O_1, O_2`;
  - departures: forward `x_1, x_2, x_3, x_4` depart from `0, C, O_1, O_2`, and backward ones from
    `I_1, I_2, C, 0`.
- So `p = p'` with no backtrack happens exactly for the *silent* transitions: forward `x_4` then forward `x_1`,
  forward `x_3` then `x_2`, backward `x_1` then backward `x_4`, backward `x_2` then backward `x_3`.
  - The other coincidences (for example forward `x_4` then backward `x_4` at position 0) reuse the unique
    `b`-edge at that position, which is a backtrack.
- A silent pair's second letter (forward `x_1`, `x_2`, backward `x_4`, `x_3`) is never a first letter (forward
  `x_4`, `x_3`, backward `x_1`, `x_2`).  So silent transitions are never adjacent.
- Cycles of `Gamma` project to cyclically non-backtracking closed walks ([FL] Lemma B, cyclically), and every such
  walk lifts back.  So `gamma = 2 min (m - #silent)` over cyclically non-backtracking closed walks of length `m`.
- Since `#silent <= m/2` and `m >= g`, this gives `g <= gamma`.  A girth cycle gives `gamma <= 2g`.
- Equality `gamma = g` needs `m = g` and `#silent = m/2`.  That is, a girth cycle whose letters pair off
  cyclically into silent pairs `x_4 x_1`, `x_3 x_2` or their inverses.

**Realizing gamma = 42.**  Let `H = <x_1, ..., x_4 | r^{21}>` with `r = x_4 x_1`.

1. *Newman's spelling theorem* (B. B. Newman, 1968).  A nonempty reduced word trivial in `H` contains a subword of
   a cyclic permutation of `r^{±21}` of length `> (20/21) * 42 = 40`.
   - Hence every nonempty reduced word of length `<= 40` is nontrivial.
   - A reduced word `w` of length 41 that is trivial would be such a subword itself.  Then `w x = R` for a cyclic
     permutation `R` of `r^{±21}` and a letter `x`, so `w = x^{-1} != 1`.
   - So no nonempty reduced word of length `<= 41` dies in `H`.
2. *Residual finiteness.*  One-relator groups with torsion are residually finite (Wise, via the quasiconvex
   hierarchy).  There are finitely many words of length `<= 41`, so some finite quotient `Q` keeps all of them
   nontrivial.
3. *The graph `Phi = Cay(Q, {x_1, ..., x_4})`.*
   - It is a 4-bouquet cover (each `x_j` acts as a permutation).
   - It has no loops, since `x_j != 1`, and girth `>= 42` by step 2.
   - `r^{21} = 1` gives a cyclically non-backtracking closed walk of length 42, so `girth(Phi) = 42`.
4. *The lift.*
   - The walk `(x_4 x_1)^{21}` has 21 silent transitions and 21 hops.
   - Each hop is `a^{O_2 - I_1}` on the current line: arrive at `I_1` by `x_1`, leave from `O_2` by `x_4`.
   - Its lift is a cycle with label `prod_{k=1}^{21} b^2 a^{O_{2,k} - I_{1,k}}`, of free-product length 42.
   - So `gamma <= 42 = g <= gamma`.

With Steenbock's rows `phi` (any injection) and this `Phi`, all his hypotheses (girth `> 41`) hold.  Then
`gamma = 42`, `q(gamma) = 11`, and the eleven-point bound of [EP] is exactly the threshold.  The silent 12-point
`S` is the set of partial sums of 11 consecutive hops `10^{5r_k - 1} - 10^{5r_k - 4}` along this cycle.  At the
other extreme, a `Phi` of girth 42 with no silent-paired girth cycles and `gamma = 84` gives `q = 24`.

## 4. Computation

`experiments/rips-segev-one-copy-2026-09-18/hop_repeats.py` (results in `hop_results.txt`):
- It builds random fixed-point-free `sigma_1, ..., sigma_4`, hill-climbed to remove short cycles.
- It computes `gamma` by 0-1 BFS over directed edges, where silent transitions cost 0 and hops cost 1.
- It computes the least hop-repeat distance `rep` the same way.
- It asserts `g <= gamma <= 2g`.

Across 16 trials (`n = 24`, `32`) it found `2 rep = gamma` every time, with no violation of Lemma 1.
