---
rg: 2
id: fpbs-tree-projected-vertical-slot-second-moment-proof
kind: route
title: Paley–Zygmund over excursion trails with oriented vertical steps, bounded by an offset-class LP capacity map
target: fpbs-tree-projected-vertical-slot-second-moment
requires:
  - fpbs-tree-projected-oriented-second-moment-thresholds
  - fpbs-tree-projected-rank-two-excursion-second-moment
artifacts:
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/engine.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/certify_v.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/blockcheck_v.py
  - experiments/tree-projected-vertical-slot-second-moment-2026-09-17/output.txt
---

Notation as in `fpbs-tree-projected-rank-two-excursion-second-moment-proof` (below:
"the base proof"). `L = {a^±1, b^±1}`, `x = 1/p`, `D_(t^-1) = -D_t`, `|D_t| = m`.
The vertical part is `{(1, ±c)}` with `c != 0`.

## 1. Ensemble

A *vertical-slot trail* of length `N` consists of a reduced word `t_1 ... t_N`, a height
`s_1 in D_(t_1)`, and for each `1 <= i <= N-1` a slot `σ_i` and a height
`s_(i+1) in D_(t_(i+1))`. The slot is a pair `(V, ε)`:
* `V in {0, 1}`;
* `ε` is empty or a triple `(e, u, u')` with `e in L \ {t_i^-1}`, `u != u'` in `D_e`,
  and `s_(i+1) != u'` if `e = t_(i+1)`.

*Walk.* From `g_i = (w_i, z)`, block `i+1` is:
* if `V = 1`, the vertical edge `(w_i, z) — (w_i, z + c)`, and then `z := z + c`;
* if `ε != ∅`, the excursion `(w_i, z) — (w_i e, z+u) — (w_i, z+u-u')`, and then
  `z := z+u-u'`;
* the step `(w_i, z) — (w_(i+1), z + s_(i+1))`.

*Excluded data.* A block whose edges are not pairwise distinct is removed from the
ensemble. For `m >= 3` and `J = 1`, `engine.first_moment_terms` finds no such
system consistent with the inequalities. `blockcheck_v.py` confirms this: the exact
weight equals the lower bound on every tested decoration.

**Lemma 1.** Edges of different blocks are different, and a trail with data
`(V_i, ε_i)` has `N + Σ (V_i + 2 [ε_i != ∅])` distinct edges. *Proof.* A step or
excursion edge of block `i+1` lies over the tree edge `{w_i, w_i f}` with
`f != t_i^-1`, as in the base proof. A vertical edge of block `i+1` lies in the fibre
of `w_i`, and no other block has a vertical edge in that fibre. Within a block,
edges are distinct by the exclusion. ∎

So `E Z_N = 4 · 3^(N-1) · m p · W^(N-1)`. Here `W` is the exact weight of one block
for a fixed next letter. It depends on the heights, and
`W >= w := engine.wblock(first_moment_terms(1, True), m, p)`. The lower bound
subtracts, for each internal coincidence system, an upper count of its solutions.

Lemma 2 of the base proof (infinite cluster) holds verbatim: deleting the last
block gives a trail of length `N`.

## 2. Pairs

For trails `γ, γ'` with common prefix length `j`, Lemma 1 gives the same structure
as in section 2 of the base proof.
* Only blocks `i <= j+1` can share edges.
* In a prefix block both trails start in the fibre of `w_(i-1)`, at heights `z` and
  `z + h`, and use the same next letter.
* A divergence block has at most 4 edges per trail, so its pair sum is at most
  `x^4 W^2`.

**Offset classes.** A prefix block starts at offset `h`. Its class is `k in {-1,0,1}`
if `h = k c`, and `G` (generic) otherwise.

**Lemma 3 (symbolic block bounds).** For each start class `s`, and each `h` in `s`:
* for each target class `j`, the pair sum over block data whose final offset lies in
  `j` is at most `T[s][j]`;
* the pair sum over data whose final offset is nonzero is at most `T[s][NZ]`.

Here `T = engine.matrix(pair_terms(1, 1, True), 4, m, p)`, a `4 x 5` array.

*Proof.* The argument is section 3 of the base proof, run by `engine.pair_terms`:
* the edges are labelled `vert`, `t`, `o1` or `o2`, and their lower and upper heights
  are linear forms in the decoration variables and in `h`, `c`;
* the inclusion identity is taken over sets `Q` of candidate pairs with the same
  label;
* the counting bound `m^comps (m-1)^fedges` is maximised over admissible free sets.

The new points are these.
1. *Class equations.* In state `k`, `h` is replaced by `k c`. In state `G`, each
   `h - k c` is added to the forbidden forms, so a configuration forcing it is
   dropped. A target class `k` adds the equation `h' - k c = 0`. Target `G` takes the
   count without an equation, and is dropped if some `h' = k c` is forced. Target
   `NZ` takes the count without an equation, and is dropped only if `h' = 0` is forced.
   Adding an equation only restricts the data, so each count is an upper bound.
2. *Forbidden forms.* The forms are `c`, the inequalities `u - u'` and `s - u'`, and
   in state `G` the forms `h - k c`. The internal coincidence systems of either trail
   are forbidden too, because such data are excluded from the ensemble.
3. *Grouping.* Subsets `Q` are enumerated by depth-first search, pruned at the first
   forced configuration. A superset of a forced `Q` is forced. Subsets are grouped by
   row space, so each distinct system is counted once with its multiplicities in
   `|Q|`.

Every term is independent of `h` within a class and of the heights. The check in
`blockcheck_v.py` is described in the target. ∎

## 3. The LP capacity map

Let `zero = 0` be the class `h = 0`. For `y in R_(>=0)^4` put

```text
Phi(y)_s = T[s][zero] y_zero + max { Σ_(j != zero) μ_j y_j : 0 <= μ_j <= T[s][j], Σ_j μ_j <= T[s][NZ] } .
```

The maximum is attained greedily in decreasing order of `y_j` (`engine.phi`). `Phi` is
monotone (`y <= y'` implies `Phi(y) <= Phi(y')`) and positively homogeneous.

**Lemma 4 (prefix sum).** Let `U_k(s)` be the supremum over `h` in class `s` of the
pair sum over `k` consecutive prefix blocks started at offset `h`. Then
`U_k <= Phi^k(1)`.

*Proof.* Induction on `k`. Split the first block's data by the final offset `h'`.
The continuation from `h'` is at most `U_(k-1)(class(h'))`. Let `μ_j` be the first
block's pair mass into class `j`. By Lemma 3, `μ_j <= T[s][j]` and
`Σ_(j != zero) μ_j <= T[s][NZ]`. So the total is at most
`μ_zero U_(k-1)(zero) + Σ_(j != zero) μ_j U_(k-1)(j) <= Phi(U_(k-1))_s`. Monotonicity
and the induction hypothesis then give `Phi(Phi^(k-1)(1))`. ∎

**Collatz–Wielandt.** Suppose `y > 0` and `Phi(y) <= θ L y` with `θ < 1`, where
`L = 3 w^2`. Put `C = 1 / min y`. Then `1 <= C y`, and so
`Phi^k(1) <= C Phi^k(y) <= C (θ L)^k y`.

## 4. Criterion

Section 4 of the base proof applies with `M_1 T^(j-1)(1,1)^T` replaced by
`M_1 · Phi^(j-1)(1)`, with `x^3` replaced by `x^4`, and with `W` in place of `w`. Here
`M_1 = (mp, 0, 0, m(m-1)p^2)`: block 1 has no slot, and both trails start at `g_0`,
so the offsets after block 1 lie in `D_(t_1) - D_(t_1)`. Their nonzero values go to
the classes `±1` or `G`; the bound puts all of that mass on the largest `y` value.
This gives

```text
E Z_N^2 / (E Z_N)^2  <=  1 + (x^4 / (4 (mp)^2)) Σ_(j>=1) (3 W^2)^(-(j-1)) max_s (M_1 Phi^(j-1)(1))
                     <=  1 + const · Σ_j θ^(j-1)   (since L = 3 w^2 <= 3 W^2),
```

which is bounded uniformly in `N`. Paley–Zygmund and Lemma 2 give `theta(p) > 0`.

## 5. Certificate (`certify_v.py`, exact rationals)

For `m = 15, 16, 17`, take `p_m = floor(10^6 p_low)/10^6`. Here `p_low < p*(m,2)` is
computed as in Part B of the base proof (`sqrt 3 < 17321/10000`, integer square root
rounded up). `certify_v.py` then does three things:
* it builds `T` and `w` exactly;
* it finds `y` by float iteration of `Phi` and rounds it to rationals with
  denominator at most `10^9`;
* it checks `Phi(y) < L y` in exact arithmetic.

The margins `1 - max_s Phi(y)_s / (L y_s)` are `6.2e-4`, `5.1e-3` and `9.2e-3`
(`output.txt`). The same check passes for `m = 18, 19, 20` and fails at `m = 14`
(margin `-4.5e-3`).

## 6. Conclusion

For `m in {15,16,17}`:
* `p_c <= p_m` by section 5;
* `p_m < p*(m,2) <= p_{2->2} <= p_u` by `fpbs-tree-projected-oriented-second-moment-thresholds`,
  whose hypotheses (rank `n = 2`, `m_hi = m`, `v = 2`) are met.

For `m >= 18`, see `fpbs-tree-projected-rank-two-excursion-second-moment`. ∎

## 7. Negative results

These are recorded in the target and in `output.txt`.
* **`m <= 14`.** No LP certificate exists at `J = 1`.
* **Two excursions per slot (`J = 2`).** The bound gets worse below `m = 16`.
* **First moment at `m = 3`.** An upper bound for `3W` at `p*(3,2)` is below 1 for
  one vertical step and at most three excursions per slot. That bound is the naive
  count with coincidences not subtracted, and `W` is increasing in `p`. So the first
  moment itself vanishes, and no second-moment refinement over these ensembles can
  reach `m = 3`.

The small-`m` range therefore needs the pattern-specific exact counts, which replace
the uniform `m^comps (m-1)^fedges`. It also needs richer vertical moves, with several
steps in both orientations.
