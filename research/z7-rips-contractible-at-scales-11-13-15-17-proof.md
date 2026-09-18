---
rg: 2
id: z7-rips-contractible-at-scales-11-13-15-17-proof
kind: route
title: Layered orbit certificates on the lifted peeling links, one per link dimension k = 2..7 and scale r = 11, 13, 15, 17, replayed point by point by an exhaustive verifier
target: z7-rips-contractible-at-scales-11-13-15-17
requires: []
artifacts: [research/z7-rips-contractible-at-scale-10-proof.md, experiments/zn-rips-layered-orbits-2026-09-18/README.md, experiments/zn-rips-layered-orbits-2026-09-18/overv.cpp, experiments/zn-rips-layered-orbits-2026-09-18/lcs2.cpp, experiments/zn-rips-layered-orbits-2026-09-18/results.txt, experiments/zn-rips-layered-orbits-2026-09-18/negative-controls.txt, experiments/zn-rips-layered-orbits-2026-09-18/certs/c7-11.txt.gz, experiments/zn-rips-layered-orbits-2026-09-18/certs/c7-13.txt.gz, experiments/zn-rips-layered-orbits-2026-09-18/certs/c7-15.txt.gz, experiments/zn-rips-layered-orbits-2026-09-18/certs/c7-17.txt.gz]
---

Notation and the reduction are as in `research/z7-rips-contractible-at-scale-10-proof.md`:
- `N[v]` is the closed `r`-neighbourhood;
- `x ≻ 0` means the last nonzero coordinate of `x` is positive;
- `hull(S)` is the smallest integer box containing `S`;
- `E = e_k`.

Its §1–§3 hold for every `(n, r)` and are used unchanged. They give the **Theorem**: if for each `k = 2, …, n` some
sequence of (D) and (K) moves starting from `C = Lmax_k = { x ∈ Z^k : |x|_1 ≤ r, x ≻ 0 }` ends at `C = {e_k}`, then
`VR(Z^n, d_1; r)` is contractible.

Only (D) moves are used here. A (D) move `x | w` requires:
- `x, w ∈ C` and `w ≠ x`;
- `w ∈ hull(0, x, E)`;
- `N[x] ∩ C ⊆ N[w]`.

It then deletes `x`. The route builds such sequences for `n = 7` and `r ∈ {11, 13, 15, 17}` out of orbit moves. Coordinates are indexed `0, …, k − 1`.

## 1. Layers and orbit moves

The **layer** `ℓ(x)` of `x ≠ 0` is the index of its last nonzero coordinate. Put `T_j = { x ∈ Lmax_k : ℓ(x) = j }`.
Let `H_j` be the group of signed permutations of coordinates `0, …, j − 1`, acting on `Z^k` and fixing the coordinates
`≥ j`. The following hold:
- each `h ∈ H_j` is a `d_1`-isometry fixing `0` and `E`, since `k − 1 ≥ j`;
- `H_j ≤ H_i` for `j ≤ i`;
- `H_j` preserves `T_i` for every `i ≥ j`, because it changes neither the layer nor the sign of the last nonzero
  coordinate;
- `H_j` preserves `hull(0, x, E)` in the sense that `h · hull(0, x, E) = hull(0, hx, E)`.

The last point holds because the box is the product of the intervals between `0` and `x_i` (with `max(x_{k−1}, 1)` in
the last factor), and `h` permutes these factors up to sign without touching the last one.

**Invariant (I).** `C ∩ T_i` is `H_i`-invariant for every `i`. It holds for `C = Lmax_k`.

**Lemma P (membership in `H_j C`).** Assume (I). Let `z ≠ 0`.
- If `ℓ(z) ≥ j`, then `z ∈ H_j C` if and only if `z ≻ 0` and `z ∈ C`.
- If `ℓ(z) < j`, then `z ∈ H_j C` if and only if some `c ∈ C` with `ℓ(c) < j` has the same multiset
  `{|c_0|, …, |c_{j−1}|}` as `z`.

*Proof.* First case. Suppose `z = hc` with `c ∈ C`. Then `c` agrees with `z` on the coordinates `≥ j`. So
`ℓ(c) = ℓ(z) = L`, `z_L = c_L > 0` and `c ∈ C ∩ T_L`. This set is `H_L`-invariant and `h ∈ H_j ≤ H_L`, so `z ∈ C`. The
converse is trivial.

Second case. Such `z` and `c` vanish from coordinate `j` on. `H_j` acts transitively on the vectors supported on
`0, …, j − 1` with a given multiset of absolute values. ∎

**Lemma O (orbit move).** Assume (I). Let `x ∈ C ∩ T_j` and `w ∈ C`, and suppose:
1. `w ∈ hull(0, x, E)` and `ℓ(w) ≥ j`;
2. `H_j w ∩ H_j x = ∅`, and `H_j x ∪ H_j w ⊆ C`;
3. `d(x, w) ≤ r`;
4. every `z ∈ H_j C` with `d(z, x) ≤ r` has `d(z, w) ≤ r`.

Then the points of `H_j x` can be deleted one at a time, in any order, by the (D) moves `hx | hw`. Afterwards
`C' = C ∖ H_j x` satisfies (I).

*Proof.* Let `C''` be the current set when `hx` is deleted, so `C' ⊆ C'' ⊆ C`. We check the three conditions of (D).
- *Membership.* `hx ∈ C''` because it has not been deleted yet. `hw ∈ C''` because `hw ∈ H_j w ⊆ C` and
  `H_j w ∩ H_j x = ∅`. For the same reason `hw ≠ hx`.
- *Box.* `hw ∈ h · hull(0, x, E) = hull(0, hx, E)`.
- *Domination.* Let `z ∈ C''` with `d(z, hx) ≤ r`. Then `h^{-1}z ∈ H_j C` and `d(h^{-1}z, x) ≤ r`. By 4,
  `d(h^{-1}z, w) ≤ r`, that is, `d(z, hw) ≤ r`. Also `hx ∈ N[hw]` by 3. So `N[hx] ∩ C'' ⊆ N[hw]`.

For (I): `C' ∩ T_i = C ∩ T_i` for `i ≠ j`. `C' ∩ T_j` is an `H_j`-invariant set minus one `H_j`-orbit. ∎

An **orbit certificate** is a list of lines `D x | w`. Line by line, starting from `C = Lmax_k`, each line must satisfy
the hypotheses of Lemma O, and its orbit `H_j x` is then deleted. By Lemma O, and induction on (I), a valid orbit
certificate expands to a plain (D) certificate. If it ends at `C = {e_k}`, the Theorem applies.

## 2. The certificates and their verification

The files `experiments/zn-rips-layered-orbits-2026-09-18/certs/c<k>-<r>.txt.gz` hold the orbit certificates for
`k = 2, …, 7` and `r = 11, 13, 15, 17`. The generator is `lcs2.cpp`, described in the README. It is not part of the
proof, since every line is checked independently.

**Verifier.** `overv.cpp` (`./overv k r cert`) keeps the current set `C` as an exact bitmap over all of
`{ z ∈ Z^k : |z|_1 ≤ r }`, through a ranking that is checked to be a bijection. It also maintains, for each `j`, the
counts of points of `C` in layers `< j` keyed by the multiset `{|c_0|, …, |c_{j−1}|}`.

For each line `D x | w` with `j = ℓ(x)`, it checks the following:
- `x, w ∈ C`, and `0 < d(x, w) ≤ r`;
- `w ∈ hull(0, x, E)`, and `ℓ(w) ≥ j`;
- it enumerates `H_j x` and `H_j w` explicitly, and checks that they are disjoint and contained in `C`;
- hypothesis 4, by exhaustive depth-first search over all `z` with `|z|_1 ≤ r` and `d(z, x) ≤ r`, testing
  `z ∈ H_j C` by Lemma P.

The search prunes a branch only when an upper bound on `d(z, w)` over its completions is `≤ r`. The bound is
`min(|z_rest| + |w_rest|, |z_rest − x_rest| + |x_rest − w_rest|)`, with the remaining norm budgets. It then deletes
every point of `H_j x` and updates the counts.

At the end it checks that `C = {e_k}`. It never uses the invariance of `C` for layers `< j`: Lemma P needs (I) only
in layers `≥ j`. That invariance is guaranteed by Lemma O and the orbit enumeration.

**Output** (`results.txt`, with `VERIFIED: ends at {e_k}` for all 24 runs):

| r | k = 7: orbit lines | k = 7: points `|Lmax_7|` | k = 7: search nodes | lines, k = 2..6 |
|---|---|---|---|---|
| 11 | 1,590 | 397,727 | 143,689,263 | 76, 237, 493, 820, 1,192 |
| 13 | 2,912 | 1,170,247 | 705,695,473 | 103, 355, 796, 1,399, 2,118 |
| 15 | 5,032 | 2,992,383 | 2,529,020,776 | 134, 506, 1,217, 2,255, 3,552 |
| 17 | 8,301 | 6,863,495 | 9,261,890,462 | 169, 694, 1,783, 3,475, 5,689 |

Each line count includes the `k − 1` final moves `e_i | e_k`, `i < k`.

**Negative controls** (`negative-controls.txt`) are one-line edits of `c6-13`. Each is rejected at the expected
line:
- a deleted line fails domination later;
- a dominator replaced by another box point fails domination;
- a duplicated line fails "x not present";
- a dominator outside `hull(0, x, E)` fails the box test.

With `n = 7`, for each `r ∈ {11, 13, 15, 17}` and each `k = 2, …, 7`, the expanded certificate is a (D) certificate on
`Lmax_k` ending at `{e_k}`. The Theorem gives the claim. ∎

## 3. Remarks (not used in the proof)

- For `k ≤ 5`, every orbit at all four scales is removed by the **level test** alone. At level `m`, this test takes
  `|w| ≤ m − 1` and checks hypothesis 4 against the superset of all `z` with `|z| ≤ m` and (`z ≻ 0` or `ℓ(z) < ℓ(x)`).
  So the certificate does not depend on the order within a level. Only `k = 6, 7` need tests against the alive orbits
  and deferral of a few dozen orbits to lower levels. See `lcs2` in the README.
- At `n = 8` the same generator stalls at every open scale tried (`8 ≤ r ≤ 14`), and so does an exact orbit greedy.
  The obstruction is recorded on the target node.
