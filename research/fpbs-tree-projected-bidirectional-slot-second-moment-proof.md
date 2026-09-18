---
rg: 2
id: fpbs-tree-projected-bidirectional-slot-second-moment-proof
kind: route
title: Paley–Zygmund over slot trails with bidirectional vertical runs, a refined nonzero capacity and rigid collision counts
target: fpbs-tree-projected-bidirectional-slot-second-moment
requires:
  - fpbs-tree-projected-vertical-slot-second-moment
  - fpbs-tree-projected-rank-two-excursion-second-moment
  - fpbs-tree-projected-oriented-second-moment-thresholds
artifacts:
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/engine_r.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/certify_r.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/blockcheck_r.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/cert_plain_R101_K1.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/cert_nzref_rigid_R101_K1.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/blockcheck_nzref_R101.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/blockcheck_nzref_rigid_R101.txt
---

Notation as in `fpbs-tree-projected-vertical-slot-second-moment-proof` (below: "the
vertical-slot proof") and its base proof
`fpbs-tree-projected-rank-two-excursion-second-moment-proof`. `L = {a^±1, b^±1}`,
`x = 1/p`, `D_(t^-1) = -D_t`, `|D_t| = m`, vertical part `{(1, ±c)}` with `c != 0`.
Only the changes to the vertical-slot proof are spelled out. Sections 3 and 4 of that
proof (the LP capacity map, Lemma 4 and the criterion) are used verbatim.

## 1. Ensemble

A *bidirectional slot trail* is a vertical-slot trail whose slot component
`V in {0, 1}` is replaced by a run `r in R = {-1, 0, 1}`. From `g_i = (w_i, z)`,
block `i+1` is:
* if `r = 1`, the edge `(w_i, z) — (w_i, z + c)`, then `z := z + c`;
* if `r = -1`, the edge `(w_i, z) — (w_i, z - c)`, then `z := z - c`;
* if `ε = (e, u, u') != ∅`, the excursion `(w_i, z) — (w_i e, z+u) — (w_i, z+u-u')`,
  then `z := z + u - u'`;
* the step `(w_i, z) — (w_(i+1), z + s_(i+1))`.

Both `(1, c)` and `(1, -c)` lie in `S`, so these are edges of the Cayley graph. The
undirected edge `{(w, l), (w, l + c)}` is the same whichever way it is traversed.
`engine_r.vrun` records it as `('vert', l, l + c)`, by its lower and upper heights with
respect to `c`. Two vertical edges in one fibre are therefore equal if and only if
their lower heights agree. This holds in particular for an upward step of one trail
and a downward step of the other.

*Excluded data.* As before, a block whose edges are not pairwise distinct is removed.
For `R = {-1, 0, 1}` and `J = 1`, `engine_r.first_moment_terms` finds no internal
coincidence system that is consistent with the inequalities and `c != 0`. All 12
terms have sign `+1`, so nothing is removed, and the one-block weight

```text
W = w := engine_r.wblock(first_moment_terms(1, (-1,0,1)), m, p)
```

is exact and independent of the heights. `blockcheck_r.py` confirms
`w_bound / w_exact = 1` on 24 decorations.

**Lemma 1.** Edges of different blocks are different, and a block has at most 4 edges.
*Proof.* A step or excursion edge of block `i+1` lies over a tree edge
`{w_i, w_i f}` with `f != t_i^-1`, as in the base proof. A vertical edge of block
`i+1` lies in the fibre of `w_i`. The `w_i` are pairwise distinct, and no other block
has a vertical edge there. Within a block the edges are distinct by the exclusion.
There are at most `1 + 2 + 1` of them. ∎

So `E Z_N = 4 · 3^(N-1) · m p · W^(N-1)`. Lemma 2 of the base proof (infinite
cluster) holds verbatim.

## 2. Symbolic block bounds

Section 2 of the vertical-slot proof carries over word for word:
* the offset classes are `k in {-K..K}` and `G`;
* the divergence block has at most 4 edges per trail, so its pair sum is at most
  `x^4 W^2`;
* the pair transfer bound `T` is a `(2K+2) x (2K+3)` array.

In particular Lemma 3 of that proof holds for
`T = engine_r.matrix(pair_terms(1, K, (-1,0,1)), 2K+2, m, p)`.

Recall how each entry is formed.
* *Inclusion identity.* For fixed data the pair weight is
  `p^(|E1| + |E2| - |E1 ∩ E2|) = p^(ne) Σ_(Q ⊆ E1 ∩ E2) (x-1)^|Q|`, where `Q` runs over
  sets of shared-edge pairs. Summing over data gives
  `Σ_Q (x-1)^|Q| p^(ne) N(Q)`. Here `N(Q)` is the number of ensemble data in which
  every pair of `Q` is shared and the target condition holds.
* *Counting bound.* `N(Q)` is bounded above by the counting bound `m^comps (m-1)^fedges`
  of section 3 of the base proof. It is applied to the linear system of `Q` together
  with the class equations, and to the inequality forest on a free set.

Every coefficient `(x-1)^|Q|` is `>= 0`, since `p <= 1`. So any valid upper bound for
each `N(Q)` gives a valid entry. The two refinements below replace the counting bound
by smaller valid upper bounds. With both flags off, `engine_r` is w5-009's engine with
the extra run `r = -1`.

## 3. Refined nonzero capacity (flag `NZREF`)

Fix a start class `s = k` (not `G`), a pair of slot structures and a set `Q`. Write
`N(Q)` for the number of ensemble data with `Q` shared, and `N_0(Q)` for those that in
addition have final offset `h' = 0`. The NZ entry needs an upper bound for
`N(Q) - N_0(Q)`, the data with `h' != 0`. The vertical-slot proof uses the counting
bound `UB(Q) >= N(Q)`.

**Lemma 5.** Let `r0` be the row space of `Q`'s equations together with `h' = 0`, and
suppose:
1. every reduced row of `r0` has the form `y - y' = 0`, with `y, y'` decoration
   variables of the same letter (`identity_lower`);
2. after identifying the variables, the inequality graph (`u != u'`, `s != u'`) has no
   loop and no cycle;
3. for every internal coincidence system `σ` of either trail, `r0 + σ` implies one of
   the forbidden equalities `y = y'` (an inequality of the ensemble) or `c = 0`
   (`no_internal`);
4. `r0` itself forces no forbidden equality.

Then `N_0(Q) = m^comps (m-1)^fedges` exactly, for the forest of condition 2. So
`N(Q) - N_0(Q) <= UB(Q) - m^comps (m-1)^fedges`.

*Proof.* By condition 1 the solutions of `r0` in `D^vars` are exactly the assignments
that are constant on the identification classes. Each class takes values in the set
of one letter, of size `m`. The ensemble conditions are:
* the inequalities, which after identification form the forest of condition 2;
* the class condition `h = k c`, which is already substituted;
* the absence of internal coincidences.

By condition 3 an internal coincidence together with `r0` forces a forbidden equality.
A solution that satisfies the inequalities and has `c != 0` therefore has none, so the
last condition is automatic. The number of assignments of a forest with `m` values per
vertex and `!=` on each edge is `m^comps (m-1)^fedges` exactly: choose a root in each
tree, then each further vertex avoids the value of its parent. ∎

The subtraction is done for every `Q` in the row-space group, with the group's
multiplicities in `|Q|`, and only when all four conditions hold (engine lines under
`if NZREF:`). In class `G` the equation `h' = 0` involves `h`, so condition 1 fails and
nothing is subtracted. Since `(x-1)^|Q| >= 0`, the refined NZ entry is still an upper
bound for the pair mass into nonzero offsets. Nothing about the decoration is used.

## 4. Rigid collision counts (flag `RIGID`; rigid decorations only)

Recall the counting bound. Choose a free set `F` of decoration variables such that the
remaining variables `Det` are determined by `F`, `h` and `c` through the system. Then
the number of solutions is at most the number of assignments of `F` that satisfy the
inequalities among `F`. That is at most `Π_trees m (m-1)^(size-1)` over a spanning
forest of the inequality graph on `F`. Determined variables are counted once each,
without using that they must lie in their own decoration set.

`count_bound_rig` does use that. It first drops rows that involve only `h` and `c`,
which only weakens the system. It then solves the system for `Det` (`_express`). If a
determined variable has the form `y = a x + gamma`, with a single free variable `x`
and `gamma = alpha c + beta h`, then `x` is confined to
`X = {x in D_x : a x + gamma in D_y}`.

**Lemma 6.** Let the decoration be rigid. Then `|X| <= m - 1` in each of these cases:
1. `a = +1` and `x`, `y` have different letters;
2. `a = -1` and `x`, `y` have the same letter;
3. `|a| != 1` and `x`, `y` have the same letter;
4. `a = +1`, same letter, and `gamma != 0` for all admissible `(h, c)`;
5. `a = -1`, different letters, and `gamma != 0` for all admissible `(h, c)`.

Here `gamma != 0` is guaranteed in two situations (`_nonzero`):
* `beta = 0` and `alpha != 0`, since `c != 0`;
* the start class is `G`, `beta != 0`, and `-alpha/beta` is an integer `k` with
  `|k| <= K`, since class `G` means `h != k c` for those `k`.

*Proof.* The three fibre letters `t`, `o1`, `o2` are distinct elements of
`L \ {t_i^-1}`. So their sets are three distinct members of
`{D_a, -D_a, D_b, -D_b}`, and by rigidity no two of these are translates. If
`|X| = m`, then `a D_x + gamma ⊆ D_y`, and since both sides have `m` elements,
`a D_x + gamma = D_y`.
* In case 1, `D_x + gamma = D_y` makes two members translates, which is impossible.
* In case 2, `-D + gamma = D` makes `D` and `-D` translates, which is impossible.
* In case 3, `diam(a D + gamma) = |a| diam D != diam D`, since `diam D > 0` (`m >= 3`).
* In case 4, `D + gamma = D` with `gamma != 0` is impossible for a finite nonempty set.
* In case 5, `-D_x = D_(x^-1)` is again a member of the set. So `-D_x + gamma = D_y`
  forces `y`'s letter to be `x^-1` and `gamma = 0`, which is excluded. ∎

For each tree of the inequality forest that contains such an `x`, root the tree at
`x`. The tree then contributes at most `(m-1) · (m-1)^(size-1)` instead of
`m (m-1)^(size-1)`. At most one gain is taken per tree (`gain_order`). The engine
maximises the resulting `(m-1)` exponent over the admissible free sets, as before. So
every entry of `T` built with `RIGID` is an upper bound for every rigid decoration.
With `NZREF`, the subtracted `N_0(Q)` of Lemma 5 is exact for all decorations, so the
two refinements combine.

(`RIGID2`, a variant where `x` is confined with the other free variables of `y` held
fixed, is valid by the same argument in cases 1–3. It gains less than `10^-3` in
`rho` and is not used below.)

## 5. Certificate (`certify_r.py`, exact rationals)

As in section 5 of the vertical-slot proof:
* `p_m = floor(10^6 p_low) / 10^6`, where `p_low < p*(m, 2)` uses
  `sqrt 3 < 17321/10000` and an integer square root rounded up;
* `T` and `w` are exact, with `K = 1` (4 classes) and `R = {-1, 0, 1}`;
* `y` comes from float iteration of `Phi`, rounded to denominators at most `10^9`;
* `Phi(y) < 3 w^2 y` is checked in exact arithmetic.

| run | `m` | `p_m` | `3w` | margin | files |
|---|---|---|---|---|---|
| plain (980 terms) | 13 | 5449/250000 | 1.07927 | 2.864e-3 | `cert_plain_R101_K1.txt` |
| plain | 14 | 10133/500000 | 1.07955 | 8.200e-3 | same |
| NZREF + RIGID (1002 terms) | 12 | 2947/125000 | 1.07894 | 2.724e-3 | `cert_nzref_rigid_R101_K1.txt` |
| NZREF + RIGID | 13 | 5449/250000 | 1.07927 | 8.071e-3 | same |
| NZREF + RIGID | 14 | 10133/500000 | 1.07955 | 1.271e-2 | same |

The certifying vectors `y` are printed in the files. The same run fails at `m = 11`,
with margin `-3.5e-3`.

**Consistency check (not part of the proof).** `blockcheck_r.py` runs the independent
C enumerator `pairx.c` on concrete decorations. It forms the exact class matrix
`E[s][j] = sup_(h in s) Σ_(h' in j) Σ_k N(h, h', k) p^k` and checks `E <= T`
entrywise at `p = 0.07` and `p = 0.28/m`.
* With NZREF, 24 decorations, `m = 3..7`: largest ratio `0.9857`.
* With NZREF and RIGID, the 20 rigid ones: largest ratio `0.9868`.
* The one-block weight is exact in every case.

## 6. Conclusion

For `m in {13, 14}` and any heights, the plain certificate gives `p_c <= p_m`. For
`m = 12` and rigid decorations, the NZREF + RIGID certificate gives `p_c <= p_m`. In both
cases `p_m < p*(m, 2) <= p_{2->2} <= p_u` by
`fpbs-tree-projected-oriented-second-moment-thresholds`, whose hypotheses (rank
`n = 2`, uniform multiplicity `m`, `v = 2`) are met. ∎

## 7. Negative results

These are recorded in the target claim:
* heights-uniform `rho > 1` at `m <= 11` for every variant;
* the loss sits in the `0 -> 0` entry and in the generic row's nonzero capacity;
* exact per-decoration transfers pass at `m >= 6` on a rigid family;
* the float obstruction for `S_rig` with one excursion per slot and any run set up to
  `-3..3` (`srig_obstruction.txt`).
