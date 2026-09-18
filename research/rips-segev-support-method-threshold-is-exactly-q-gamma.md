---
rg: 2
id: rips-segev-support-method-threshold-is-exactly-q-gamma
kind: claim
title: In a Rips--Segev chain of length q(gamma) the q(gamma) hop lines are pairwise distinct, because a repeated hop line closes a cycle shorter than gamma; so every element of k[a^S <b>] with |S| <= q(gamma) is regular in Steenbock's core, and the support method stops exactly at |S| = q(gamma) + 1
distinct_from:
  rips-segev-steenbock-few-line-a-supports-are-regular: that gets q(g) distinct hop lines from the girth g of Phi, via Lemmas B and C, and needs Phi loopless; this gets q(gamma) of them from gamma directly, with no hypothesis on Phi. Since g <= gamma <= 2g, q(gamma) can be as large as q(2g), e.g. q(84) = 24 for g = 42.
  rips-segev-steenbock-eleven-point-a-supports-are-regular: that settles |S| <= 11 = q(42); this settles |S| <= q(gamma) for the actual gamma of the chosen Phi. It also shows that gamma = 42 does occur, so 11 cannot be improved uniformly in Phi, and that the silent supports of size q(gamma) + 1 found there mark the exact threshold.
  rips-segev-sparse-a-support-elements-are-regular: that is the chain criterion used here as a black box.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this closes its "12..q(gamma)" support gap.
artifacts:
  - experiments/rips-segev-one-copy-2026-09-18/hop_repeats.py
  - experiments/rips-segev-one-copy-2026-09-18/hop_results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-support-method-threshold-is-exactly-q-gamma-proof`.

**Setting.**  As in `rips-segev-steenbock-few-line-a-supports-are-regular` ([FL]).
- `Gamma` is a generalized Rips--Segev graph with `Gr'_*(1/8)`, and `K` is its core.
  `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2`.
- `gamma` is the least free-product length of a cycle label of `Gamma`.
- `q(x) = floor((floor(5x/8) - 3)/2)`.
- `N_S = (S - S) \ {0}`, and `L_S` is the set of lines `i` with `N_S ∩ Dist_i != ∅`.

**Theorem.**
1. *(Hop lines are distinct.)*  Let `P` be a backtrack-free path of `Gamma` with label
   `b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}` and `q <= q(gamma)`.  Then the lines `l_1, ..., l_q` that
   carry the syllables `a^{n_1}, ..., a^{n_q}` are pairwise distinct.  This needs no hypothesis on `Phi`: no girth
   bound and no looplessness.
2. *(Regularity.)*  Let `beta = sum_{i in S, j in J} c_ij a^i b^j != 0`.  If `|L_S| < q(gamma)`, then `beta`
   is a non-zero-divisor in `k[K]` and in `k[G(Gamma)]`.  The same holds for `sum c_ij b^j a^i` and for all
   translates.
3. *(Steenbock's graphs.)*  Rows are super-increasing, so `|L_S| <= |S| - 1`.  Hence every nonzero element
   supported on `a^S <b>` or `<b> a^S` with `|S| <= q(gamma)` is regular.
4. *(Exact threshold.)*  The previous lane's silent support has `|S| = q(gamma) + 1`.  It is read off a shortest
   cycle and is an `(N_S, N_J)`-chain of length `q(gamma)`.  So the chain criterion settles every `S` with
   `|S| <= q(gamma)` and is silent at `|S| = q(gamma) + 1`.  The gap `12..q(gamma)` left by the eleven-point node
   is closed.
5. *(On gamma = 42.)*  `gamma` depends on `Phi`, which Steenbock's data leaves free.
   - In general `g <= gamma <= 2g` with `g = girth(Phi)`.  Moreover `gamma = g` exactly when some girth cycle of
     `Phi` reads a cyclic product of the blocks `(x_4 x_1)^{±1}` and `(x_3 x_2)^{±1}`.
   - `gamma = 42` is realized.  Take `Phi = Cay(Q, {x_1, ..., x_4})` for a finite quotient `Q` of
     `<x_1, ..., x_4 | (x_4 x_1)^{21}>` in which no nontrivial reduced word of length `<= 41` dies.  Such a `Q`
     exists by Newman's spelling theorem and Wise's residual finiteness of one-relator groups with torsion.
     Then `girth(Phi) = 42`, and the walk `(x_4 x_1)^{21}` lifts to a cycle of label
     `prod_{k=1}^{21} b^2 a^{O_2 - I_1}`, so `gamma = 42`.
   - For such `Phi`, the answer to the brief's question (1) is yes: 12-point supports are exactly at the threshold,
     and the silent 12-point `S` is the set of partial sums of eleven consecutive hops `O_2 - I_1` of this cycle.
   - For a `Phi` with `gamma > 42`, part 3 settles every `|S| <= q(gamma)`.  This covers `12 <= |S| <= 24` when
     `gamma = 84`.

**Mechanism.**
- Suppose `l_s = l_t` with `s < t`.  The subpath of `P` between the two hops leaves line `l` and returns to it.
- Close it with the `a`-segment of `l` joining its ends, or cyclically reduce it if the ends coincide.  The result
  is a cycle of `Gamma` of free-product length `<= 2(t - s) <= 2(q - 1)`.
- But `2(q(gamma) - 1) <= floor(5 gamma / 8) - 5 < gamma`, which contradicts the minimality of `gamma`.
- [FL] routed the same distinctness through the projection to `Phi`, so it could only use `girth(Phi) <= gamma`.

**What this leaves.**
- Every support method stops at `|S| = q(gamma) + 1`.  There the cancellation pattern of `alpha beta = 0` must be
  used.
- The coefficient contradiction for configurations inside one copy of `Gamma` is
  `rips-segev-one-copy-configurations-carry-no-zero-divisors`.

**Calibration.**  `experiments/rips-segev-one-copy-2026-09-18/hop_repeats.py` computes, over closed
non-backtracking walks of random 4-bouquet covers `Phi` (Steenbock's gluing and silent transitions):
- `gamma = 2 * (min #hops)`;
- the least hop-repeat distance `rep`.

It asserts `g <= gamma <= 2g`.  Output is in `hop_results.txt`:
- seed 2: `n = 24`, `girth(Phi) = 3`, 12 trials;
- seed 3: `n = 32`, 4 trials.

In all 16 trials `2 * rep >= gamma` held, with equality every time.  So the bound of part 1 is attained: a shortest
cycle repeats its first hop line after `gamma / 2` hops.  The theorem is proved, not inferred from these runs; the
girths reachable at this size are small.
