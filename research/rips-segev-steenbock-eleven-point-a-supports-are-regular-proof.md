---
rg: 2
id: rips-segev-steenbock-eleven-point-a-supports-are-regular-proof
kind: route
title: Pick one pair of S per line of L_S; a cycle of these pairs would give a signed sum of distinct-row differences equal to zero, which super-increasing rows forbid, so the pairs form a forest and |L_S| <= |S| - 1
target: rips-segev-steenbock-eleven-point-a-supports-are-regular
requires: [rips-segev-steenbock-few-line-a-supports-are-regular]
---

**Conventions.**  [FL] is `rips-segev-steenbock-few-line-a-supports-are-regular` and its proof file.  [SP] is
`rips-segev-sparse-a-support-elements-are-regular-proof`.  We use the notation of [FL]: `Dist_i`, `N_S`, `L_S`, `q(x) = floor((floor(5x/8) - 3)/2)` (nondecreasing), `q(42) = 11`, and
`gamma = gamma(Gamma)`, the least free product length of a cycle label of `Gamma`.  [FL] §3 gives
`gamma >= g := girth(Phi)`, and [FL] §4 proves regularity whenever `|L_S| < q(g)`.  `Dist_i^+` is the set of
positive elements of `Dist_i`.

## 1. Super-increasing rows

**Lemma 1.**  In Steenbock's table, the line `i` with row `r = phi(i)` has
`Dist_i^+ ⊆ [10^{5r-4}, 10^{5r}]`.  If `r' < r`, then `10^{5r-4} > sum_{r'' = 1}^{r-1} 10^{5r''}`.

*Proof.*
- The positions are `0 < 10^{5r-4} < ... < 10^{5r}`.  The positive differences are `10^e` and `10^e - 10^{e'}`,
  with `5r - 4 <= e' < e <= 5r`.
- The least is `10^{5r-4}`, since `10^e - 10^{e'} >= 9 * 10^{e'} >= 9 * 10^{5r-4}`.  The largest is `10^{5r}`.
- `sum_{r''=1}^{r-1} 10^{5r''} < 10^{5r-5} * (1 - 10^{-5})^{-1} < 2 * 10^{5r-5} < 10^{5r-4}`. ∎

Call a family of lines *super-increasing* if it can be ordered `i_1, i_2, ...` with
`min Dist_{i_t}^+ > sum_{s < t} max Dist_{i_s}^+`.  By Lemma 1 and injectivity of `phi`, ordering the lines by row
makes Steenbock's lines super-increasing.  Only this property is used below.

**Lemma 2.**  Let the lines be super-increasing.  Let `i_1, ..., i_m` be pairwise distinct lines with `m >= 1`,
`d_t in Dist_{i_t}^+`, and signs `eps_t in {±1}`.  Then `sum_t eps_t d_t != 0`.

*Proof.*  Let `i_T` be the line that comes last in the order.  Then
`|sum_{t != T} eps_t d_t| <= sum_{t != T} max Dist_{i_t}^+ < min Dist_{i_T}^+ <= d_T`. ∎

## 2. The counting lemma

**Lemma 3.**  Let the lines be super-increasing.  For every finite `S ⊂ Z`, `|L_S| <= |S| - 1`.  (If `|S| <= 1`,
then `L_S = ∅`.)

*Proof.*
- For each `i in L_S` choose `s_i, s'_i in S` with `d_i := s'_i - s_i in Dist_i^+`.  This is possible since
  `Dist_i` is symmetric.
- Let `F` be the graph with vertex set `S` and an edge `E_i = {s_i, s'_i}` for each `i in L_S`.
- *No loops.*  `d_i > 0`, so `s_i != s'_i`.
- *No repeated edges.*  Suppose `E_i = E_j` with `i != j`.  Then `d_i = d_j`, so `d_i - d_j = 0`, contradicting
  Lemma 2 with `m = 2`.
- *No cycles.*  Let `E_{i_1}, ..., E_{i_m}` (`m >= 3`, distinct lines) be a cycle, traversed through vertices
  `x_0, x_1, ..., x_m = x_0`.
  - Each step `x_{t-1} -> x_t` along `E_{i_t}` changes the value by `eps_t d_{i_t}` for a sign `eps_t`.
  - Summing around the cycle gives `sum_t eps_t d_{i_t} = x_m - x_0 = 0`, contradicting Lemma 2.
- So `F` is a forest on `|S|` vertices, and its `|L_S|` edges number at most `|S| - 1`. ∎

**Sharpness of Lemma 3.**  Take distinct lines `i_1, ..., i_m`, values `d_t in Dist_{i_t}^+`, and
`S = {0, d_1, d_1 + d_2, ..., d_1 + ... + d_m}`.
- The partial sums are pairwise distinct by Lemma 2.
- Consecutive differences give `i_t in L_S`, so `|L_S| >= m = |S| - 1`.
- Hence equality holds.

## 3. The theorem

**Theorem.**  Let `Gamma` be Steenbock's explicit graph, or any graph with Steenbock's gluing pattern, `Gr'_*(1/8)`,
super-increasing lines and a loopless `Phi` of girth `g`.  Let `beta = sum_{i in S, j in J} c_ij a^i b^j != 0` with
`|S| <= q(g)`.  Then `beta` is a non-zero-divisor in `k[K]` and in `k[G(Gamma)]`, for every field `k`.  The
same holds for `sum c_ij b^j a^i` and for every translate `x beta y`.

*Proof.*  By Lemma 3, `|L_S| <= |S| - 1 < q(g)`.  Apply the theorem of [FL] §4, together with its mirror-form and
translate paragraph. ∎

For Steenbock's graphs `g >= 42`, so `q(g) >= 11`, and every `beta` with `|S| <= 11` is regular.

**Combined bound.**  [FL] also bounds `|L_S|` by the number of rows `r` with `10^{5r-4} <= max S - min S`.
- So `beta` is regular as soon as `min(|S| - 1, #{r : 10^{5r-4} <= span S}) <= 10`.
- Hence the support of the `a`-exponents of a zero divisor of this form has at least 12 points and span at least
  `10^{51}`.

## 4. How far the support method can go

The chain criterion ([SP] Theorem 2) asks for chains of length `q(gamma)`, where `g <= gamma <= 2g`.
- *Upper bound on gamma.*  A shortest cycle of `Phi` lifts, via the bijection `E` of [FL] §1, to a cycle of
  `Gamma` with `g` `b`-edges.  It has at most `g` `a`-syllables, so `gamma <= 2g`.
- *A silent support.*  Let `c` be a shortest relator cycle.  It has `gamma/2 >= q(gamma)` `a`-syllables, read
  cyclically.
  - Put `q = q(gamma)` and read `q` consecutive complete blocks `b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}` along
    `c`.  Each `|e_k| <= 2` by [FL] Lemma A(b).
  - Put `S = {0, n_1, n_1 + n_2, ..., n_1 + ... + n_q}` and `J = {0, 1, 2}`.  Then `N_S ∋ n_k`, and
    `N_J = {±1, ±2} ∋ e_k`.
  - So the segment is an `(N_S, N_J)`-chain of length `q(gamma)`, and the criterion is silent for this `S`.  Here
    `|S| <= q(gamma) + 1 <= q(2g) + 1`, which is 25 for `g = 42`.
- *The gap.*  Supports with `q(g) + 1 <= |S| <= q(gamma)` are not settled here.  For them, a chain of `q(gamma)`
  hops exists only if its hop lines repeat at walk distance `>= g`.  If `gamma = g`, the gap is empty and the bound
  `|S| <= q(g)` is exactly the limit of the support method.

## 5. Calibration

`experiments/rips-segev-eleven-point-2026-09-18/rainbow_forest.py` (`results.txt`, seeds 1--3):
- It checks the Rips--Segev distinctness of all differences and the super-increasing inequality for rows 1--40.
- It generates 20000 sets `S` per seed, with 2--14 points built from Dist-steps and cycle-closing attempts, and
  asserts `|L_S| <= |S| - 1`.  Equality is attained, and there are no violations.
- It builds the sharpness sets of §2 (after Lemma 3), with `|S| = 12` and `|L_S| = 11`.
