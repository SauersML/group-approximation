---
rg: 2
id: fpbs-tree-projected-rank-two-excursion-second-moment-proof
kind: route
title: Paley–Zygmund over excursion trails with a lumped same-fibre transfer matrix, against the non-backtracking resolvent
target: fpbs-tree-projected-rank-two-excursion-second-moment
requires:
  - fpbs-tree-projected-oriented-second-moment-thresholds
artifacts:
  - experiments/tree-projected-excursion-second-moment-2026-09-17/criterion.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/certify.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/blockcheck.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/pathcheck.py
  - experiments/tree-projected-excursion-second-moment-2026-09-17/output.txt
---

Notation as in the target. Elements of `Gamma = F_2 x Z` are pairs `(w, z)`, and
`(w,z)(t,k) = (wt, z+k)`. Call `z` the *height* and `{w} x Z` the *fibre* of `w`. Let
`L = {a, a^-1, b, b^-1}` and `D_(t^-1) = -D_t`. Put `b = 3` (branching of the tree),
`E = 3` (letters other than one excluded letter) and `x = 1/p`.

## 1. Subgraph and excursion trails

**Subgraph.** Put `m = m_lo`. Choose `D'_t ⊆ D_t` with `|D'_t| = m` for `t in {a,b}`,
and put `D'_(t^-1) = -D'_t`. Let `G'` be the spanning subgraph with edges
`{g, g(t,k)}`, `k in D'_t`. Then `p_c(G) <= p_c(G')`. Vertical generators are not used.

**Data.** For `N >= 1` an *excursion trail* of length `N` consists of:
* a reduced word `t_1 ... t_N` over `L`;
* a height `s_1 in D'_(t_1)`;
* for every `1 <= i <= N-1`, a *slot* `σ_i` and a height `s_(i+1) in D'_(t_(i+1))`.

A slot is either empty or a triple `(e, u, u')` with `e in L \ {t_i^-1}`,
`u, u' in D'_e` and `u != u'`. If `e = t_(i+1)`, we also require `s_(i+1) != u'`.

**Walk.** Put `w_i = t_1...t_i`, `g_0 = (1, 0)` and `g_1 = (t_1, s_1)`. Let
`g_i = (w_i, z)`. Block `i+1` consists of slot `i` and step `i+1`.
* *Empty slot.* The block is the single edge from `g_i` to `g_(i+1) = (w_(i+1), z + s_(i+1))`.
* *Slot `(e,u,u')`.* The block is the three edges
  `(w_i, z) — (w_i e, z+u) — (w_i, z+u-u') — (w_(i+1), z+u-u'+s_(i+1))`.
  The middle edge is `g(e,u')^(-1)`, an edge of `G'`.

**Lemma 1 (distinct edges).**
* Every edge of block `i` lies over a tree edge `{w_(i-1), w_(i-1) f}` with
  `f in L \ {t_(i-1)^-1}`, so it joins depth `i-1` to depth `i`. Hence edges of
  different blocks are different.
* Inside a block, the first two edges have different lower endpoints `z` and
  `z+u-u'`. The step edge has lower endpoint `z+u-u'`. If `e != t_(i+1)`, it lies over
  a different tree edge from the middle edge. If `e = t_(i+1)`, its upper height
  `z+u-u'+s_(i+1)` differs from `z+u` because `s_(i+1) != u'`.

So a trail with `k` nonempty slots has `N + 2k` pairwise distinct edges, and is open
with probability `p^(N+2k)`. It is not always self-avoiding: the top of an excursion
along `t_(i+1)` is a vertex of the next fibre. That does not matter. `pathcheck.py`
enumerates all 280908 trails of length 3 for `m = 3` and confirms the edge structure and
the count below.

**First moment.** Let `Z_N` be the number of open excursion trails of length `N`. There
are `4 · 3^(N-1)` reduced words. For a fixed next letter, the weighted count of
choices for one block is

```text
w = m p + m (m-1)^2 p^3 + (E-1) m^2 (m-1) p^3 .
```

* Empty slot: `m` choices, one edge.
* Slot with `e = t_(i+1)`: `u != u'` and `s != u'`, three edges.
* Slot with one of the other `E-1` letters: `u != u'`, three edges.

So `E Z_N = 4 · 3^(N-1) · mp · w^(N-1)`.

**Lemma 2 (infinite cluster).** Deleting block `N+1` from a trail of length `N+1` leaves
a trail of length `N`, and the edges are a subset. So the events `{Z_N > 0}` decrease
in `N`. On `∩_N {Z_N > 0}` the cluster of `g_0` contains vertices over words of every
length, so it is infinite. Hence `P(Z_N > 0) >= 1/C` for all `N` gives `theta(p) >= 1/C > 0`.

## 2. Where two trails share edges

Let `γ, γ'` be trails with words `t, t'` and longest common prefix length `j`. Then
`E[1_γ 1_γ'] = p^(|γ| + |γ'|) x^(sh)`, where `sh` is the number of common edges.
* By Lemma 1, an edge of block `i` of `γ` can equal an edge of block `i'` of `γ'` only
  if `i = i'` and `w_(i-1) = w'_(i-1)`, that is, `i <= j+1`. `pathcheck.py` confirms
  this on 400000 random pairs.
* Within a block, edges of one trail are distinct. So `sh` is the number of pairs
  `(edge of γ, edge of γ')` that are equal.

**Prefix blocks.** A block `i` with `2 <= i <= j` is a *prefix block*. Both trails
start it at the fibre of `w_(i-1)`, at heights `z` and `z' = z + h`. Both slots use
letters from the same set `L \ {t_(i-1)^-1}`, and both steps use `t_i`. Block 1 has no
slot.

**Divergence block.** Block `j+1` (when `j < N`) is the divergence block. Each trail has
at most 3 edges there, so `sh <= 3` for it. Its pair sum is at most `x^3 w^2`, whatever
`h` is.

## 3. The lumped transfer matrix

Fix a prefix block and the offset `h` at its start. The *pair sum into a class* is the
sum of `p^(|block| + |block'|) x^(sh in block)` over pairs of block data whose final
offset lies in that class. The classes are `h' = 0` and `h' != 0`.

**Lemma 3.** For every prefix block:
* if `h = 0`, the pair sums into `h' = 0` and `h' != 0` are at most `alpha` and `beta`;
* if `h != 0`, they are at most `gamma` and `delta`.

Here `T = [[alpha, beta], [gamma, delta]]` is the matrix computed by
`criterion.matrix(terms(3), m, p)`. Each entry is a finite sum of terms

```text
mult · p^(ne) · (x-1)^(|Q|) · m^(comps) · (m-1)^(fedges),
```

and the proof of Lemma 3 is the enumeration that `criterion.terms` performs.

*Pair types.* Classify each trail's block by its slot:
* `none`;
* `Et` (letter `t_i`);
* `Eo` (one of the `E-1` other letters).

An `Eo`/`Eo` pair uses either the same letter or two different letters. That gives
10 pair types, with multiplicities `1, 1, E-1, 1, 1, E-1, E-1, E-1, E-1, (E-1)(E-2)`.

*Variables.* Each block has decoration variables `(u, u', s)` for `γ` and `(U, U', S)`
for `γ'` (only `s` or `S` for `none`), plus the parameter `h`.
* An edge is recorded by its tree-edge label (`t_i`, or the excursion letter) and its
  lower and upper heights. These are linear forms with coefficients `0, ±1`:
  * `z, z+u, z+u-u', z+u-u'+s` for `γ`;
  * the same with `h` added for `γ'`.
* Two edges are equal iff they have the same label and both heights are equal. That is
  a system of two linear equations.

*Inclusion identity.* Let `P` be the set of candidate pairs (same label). Since `x >= 1`,

```text
sum_(data) x^(sh) = sum_(Q ⊆ P) (x-1)^(|Q|) #{data : every pair in Q is equal}.
```

The same holds for each class, with the class condition added to the count.

*Counting bound.* Fix `Q` and the class. The equations form a homogeneous linear
system over `Q`, of rank `r` in the `k` decoration columns.
* Let `F` be a set of `k - r` variables whose complementary columns have rank `r`.
  Then `h` and the values on `F` determine the other variables uniquely.
* The inequality constraints `u != u'` and `s != u'` (the latter for `Et`) join two
  variables ranging over the same set `D'_e`. Take a spanning forest of those among
  `F`, with `fedges` edges and `comps = k - r - fedges` components.
* Assign values tree by tree, root first. This gives at most
  `m^(comps) (m-1)^(fedges)` solutions for each fixed `h`.

`count_bound` maximises `fedges` over all admissible `F`.

*Forced configurations.* A term is dropped, which is valid for every `h` in its state,
in three cases:
* the equations imply `u - u' = 0` or `s - u' = 0` (the latter for `Et`);
* in state `h != 0`, the equations imply `h = 0`;
* for class `h' != 0`, the equations imply the return equation `h' = 0`.

The return equation is `z_end - z'_end = 0`. For class `h' = 0` it is added to the
system. For class `h' != 0` the count is taken without it, which is an upper bound.
In state `h = 0` the parameter `h` is set to `0`.

Every term is independent of `h`, so the bounds are uniform over `h != 0`.
`blockcheck.py` compares `T` with brute-force block sums on six concrete decorations of
`F_2 x Z` (`m = 3, 4`, `|h| <= 12`, `p = 1/10`). The bounds hold in every case, e.g.
`alpha = 0.362` against `0.350`.

**Lemma 4 (prefix sum).** Let `u_0 = (1,1)` and `u_k = T u_(k-1)`. For `k` consecutive
prefix blocks starting at offset `h`, the pair sum over all data is at most `u_k(0)` if
`h = 0`, and at most `u_k(1)` if `h != 0`.

*Proof.* Induction on `k`. Split the first block's data by its final class, and bound
the continuation by the induction hypothesis for that class. The first block's pair sum
into each class is bounded by Lemma 3. Every quantity is nonnegative. No monotonicity
between `u(0)` and `u(1)` is needed. ∎

Block 1 starts at `h = 0` (both trails at `g_0`). It contributes the row vector
`M_1 = (m p^2 x, m(m-1) p^2) = (mp, m(m-1)p^2)`.

## 4. Second moment and criterion

Group pairs of trails by `j`.
* *`j = 0`.* No edges are shared, and the contribution is at most `(E Z_N)^2`.
* *`1 <= j < N`.* There are at most `4·3^(j-1) · 3^(2(N-j))` word pairs.
  * Blocks `1..j` contribute at most `M_1 T^(j-1) (1,1)^T`.
  * The divergence block contributes at most `x^3 w^2`.
  * Blocks after it share nothing and contribute `w^(2(N-j-1))`.
* *`j = N`.* Blocks `1..N` contribute at most `M_1 T^(N-1)(1,1)^T`.

Divide by `(E Z_N)^2 = 16 · 9^(N-1) (mp)^2 w^(2(N-1))`. This gives

```text
E Z_N^2 / (E Z_N)^2 <= 1 + (x^3 / (4 (mp)^2)) · sum_(j>=1) M_1 (T / (3 w^2))^(j-1) (1,1)^T ,
```

which is bounded uniformly in `N` when `rho(T) < L := 3 w^2`. Here `x^3 >= 1` also
covers the `j = N` term. `T` is nonnegative. For a nonnegative `2 x 2` matrix,
`rho(T) < L` iff `L > alpha`, `L > delta` and `(L-alpha)(L-delta) > beta gamma`. That is
`criterion(...)`.

**Proposition.** If the criterion holds at `p`, then Paley–Zygmund and Lemma 2 give
`theta_(G')(p) > 0`. Hence `p_c(G) <= p`.

*Calibration.* With excursions switched off (`terms(E, False)`), the same machinery gives
exactly `p > [3m - 1/2]^(-1)`. That is the bound of
`fpbs-tree-projected-oriented-second-moment-thresholds` without its torsion refinement,
and the script reproduces it.

## 5. The certificate (`certify.py`, exact rationals)

**Part A (tail).** At `p = c_0/m` with `c_0 = 7/25`, each term is a Laurent
polynomial in `m`, and so are `L - alpha`, `L - delta` and
`(L-alpha)(L-delta) - beta gamma`. Each has top degree `0` and positive top coefficient.
* If `f = sum_(k <= 0) a_k m^k`, then `f(m) >= a_0 - sum_(k<0) |a_k| M^k` for `m >= M`.
* At `M = 40` the certified margins are `0.00899`, `0.2335` and `0.000664`.

So the criterion holds at `p = 7/(25m)` for every `m >= 40`. This proves item 1 of the
target.

**Part B (range).** Take `3 <= m < 40` and `v in {0, 2}`, with `d = 4m + v`.
* A rational `p <= p*(m,v)` is obtained from `sqrt 3 < 17321/10000` and an integer
  square root: `p* = 2/(lam + sqrt(lam^2 - 4(d-1)))`, with `lam = v + 2 sqrt(3) m`.
* The criterion is checked exactly at `p`. It holds for `9 <= m <= 39` (`v = 0`) and
  `18 <= m <= 39` (`v = 2`).

**Part C (tail against `p*`).** `p* >= 2/(2 lam) = 1/lam`, and
`c_0 / m < 1/(v + 2 sqrt(3) m)` iff `m (1 - 2 sqrt(3) c_0) > v c_0`. Since
`1 - 2 sqrt(3) c_0 > 0.0300`, this holds for `m >= 10v`.

## 6. Conclusion

By `fpbs-tree-projected-oriented-second-moment-thresholds`, which applies to every
`n >= 2`, `p* <= p_{2->2} <= p_u`, where `p*` is the smallest root of
`(d-1)p^2 - lam p + 1` with `lam = v + 2 sqrt(3) m_hi`. The root is real:
`d - 1 <= v + 4 m_hi - 1`, and

```text
lam^2 >= v^2 + 12 m_hi^2 = (v-2)^2 + 4v - 4 + 12 m_hi^2 >= 4v - 4 + 16 m_hi >= 4(d-1)
```

for `m_hi >= 2`. Then `p* = 2/(lam + sqrt(lam^2 - 4(d-1))) >= 1/lam`.

* *Items 2 (`v = 0`, `m >= 9`) and (`v = 2`, `m >= 18`).* Part B gives, for `m < 40`, a
  rational `p <= p*` at which the criterion holds, so `p_c <= p`. Also `p <= p* <= p_u`.
  Strictness: Part B uses `p` strictly below `p*`, because `17321/10000 > sqrt 3` and
  the square root is rounded up and then truncated. For `m >= 40`, Part A gives
  `p_c <= 7/(25m) < 1/lam <= p*`, using Part C with `v <= 2 < m/10`.
* *Item 2 (arbitrary `v`, `m >= max(40, 10v)`).* Parts A and C.
* *Item 3.* `p_c <= 7/(25 m_lo)` by Part A, and `p_u >= 1/(v + 2 sqrt(3) m_hi)`.

So `p_c < p_u` in every listed case. ∎
