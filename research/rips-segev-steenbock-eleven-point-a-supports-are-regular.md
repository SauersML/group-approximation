---
rg: 2
id: rips-segev-steenbock-eleven-point-a-supports-are-regular
kind: claim
title: In Steenbock's explicit Rips--Segev core every element of k[a^S <b>] with at most 11 distinct a-exponents is a non-zero-divisor, whatever their spread, because hop lines of distinct rows cannot close a cycle on S, so |L_S| <= |S| - 1
distinct_from:
  rips-segev-steenbock-few-line-a-supports-are-regular: that proves regularity when |L_S| <= 10 and deduces it for a-span below 10^51; this proves |L_S| <= |S| - 1 for every finite S, so it covers every S with at most 11 points, of any span (e.g. S = {0, 10^60, 10^60 + 10^100, ...}), which the span bound does not.
  rips-segev-sparse-a-support-elements-are-regular: that needs (S - S) to miss Dist(Gamma) entirely; here S - S may meet the Dist sets of up to 10 lines.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this settles every element of the form sum_{i in S, j in J} c_ij a^i b^j (or b^j a^i) with |S| <= 11.
artifacts:
  - experiments/rips-segev-eleven-point-2026-09-18/rainbow_forest.py
  - experiments/rips-segev-eleven-point-2026-09-18/results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-steenbock-eleven-point-a-supports-are-regular-proof`.

**Setting.**  As in `rips-segev-steenbock-few-line-a-supports-are-regular` (cited as [FL]).
- `K` is the core of Steenbock's explicit generalized Rips--Segev graph `Gamma` (arXiv:1307.0981, "Explicit
  constructions"), with `girth(Phi) >= 42`.  `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2`.
- Line `i` has row `r = phi(i)` (`phi` injective) and distinguished positions `0, 10^{5r-4}, ..., 10^{5r}`.
  `Dist_i` is the set of differences of two of them.
- `N_S = (S - S) \ {0}` and `L_S = {i : N_S ∩ Dist_i != ∅}`.

**Theorem.**
1. *(Counting lemma.)*  For every finite `S ⊂ Z`, `|L_S| <= |S| - 1`.
2. *(Regularity.)*  Let `k` be a field, `S, J ⊂ Z` finite with `|S| <= 11`, and
   `beta = sum_{i in S, j in J} c_ij a^i b^j != 0`.  Then `beta` is a non-zero-divisor in `k[K]` and in
   `k[G(Gamma)]`.  The same holds for `sum c_ij b^j a^i` and for every translate `x beta y`.

More generally, (1) holds for any generalized Rips--Segev graph whose lines can be ordered with *super-increasing
rows*: `min Dist_i^+ > sum_{j < i} max Dist_j^+`.  Steenbock's table satisfies this, since
`min Dist_r^+ = 10^{5r-4} > sum_{r' < r} 10^{5r'}`.  With [FL], `|L_S| <= |S| - 1 < q(g)` gives regularity for
`|S| <= q(g)` in any such graph with Steenbock's gluing pattern and a loopless `Phi` of girth `g`.

**Mechanism.**
- Give each line `i in L_S` one pair `{s_i, s'_i} ⊆ S` with `|s_i - s'_i| in Dist_i`.  This is a graph on `S`
  with `|L_S|` edges, one per line and so one per row.
- Going around a cycle of this graph gives `sum ± |s_i - s'_i| = 0` over distinct rows.  The largest row's term
  exceeds the sum of all the others, so no cycle exists.
- So the graph is a forest on `|S|` vertices and has at most `|S| - 1` edges.
- For `|S| <= 11` this gives `|L_S| <= 10 < 11 = q(42)`, and [FL] applies.

**Examples now covered.**
- Every `beta` with at most 11 distinct `a`-exponents in the form `sum_j u_j(a) b^j`, with any number of layers,
  any `b`-exponents and any coefficients.
- Examples: `1 + a^{10^{60}} + a^{10^{60} + 10^{100}} + b + b^{-7}`, and every element `u(a) + w(a) b` with
  `|supp u ∪ supp w| <= 11`.
- Neither the span bound nor the sparse criterion covers these when the spread is large and `N_S` meets `Dist`.
- Three-term elements `1 + c a^d + c' b` need only `|S| = 2`.  For these, the Rips--Segev condition alone gives
  `|L_S| <= 1`.

**Limit of the support method.**
- Read `q(gamma)` consecutive hops `n_k` off a shortest relator cycle, where `gamma <= 2 girth(Phi)` is the least
  cycle length.  Put `S = {0, n_1, n_1 + n_2, ...}` and `J = {0, 1, 2}`.  Then that segment is an
  `(N_S, N_J)`-chain of the length the chain criterion needs, so the criterion is silent at this `S`.
- Here `|S| <= q(gamma) + 1 <= 25` for `g = 42`, and `|S| = 12` exactly if `gamma = 42`.  Beyond that bound the
  coefficients must enter.
- The script realizes `|S| = 12`, `|L_S| = 11`, so Lemma (1) is sharp.

**Calibration.**  `experiments/rips-segev-eleven-point-2026-09-18/rainbow_forest.py` (seeds 1--3, `results.txt`):
- It checks the Rips--Segev condition and super-increasing rows for rows 1--40.
- It builds 60000 sets `S` (2--14 points) designed to hit many rows and to close cycles.  The maximum of
  `|L_S| - (|S| - 1)` is 0 in every run, with equality attained.
- The sharpness example gives `|S| = 12`, `|L_S| = 11`.

**Not covered.**  Elements with `|S| >= 12` and `|L_S| >= 11`, such as contiguous `S` of span `>= 10^{51}`.  There
the chain criterion is silent, and the coefficients must enter.
