---
rg: 2
id: fpbs-tree-projected-pollard-slot-second-moment-proof
kind: route
title: Slot second moment with Pollard pair counts and non-AP collision counts for rigid decorations
target: fpbs-tree-projected-pollard-slot-second-moment
requires:
  - fpbs-tree-projected-bidirectional-slot-second-moment
  - fpbs-tree-projected-vertical-slot-second-moment
  - fpbs-tree-projected-oriented-second-moment-thresholds
artifacts:
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/engine_p.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/certify_p.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/blockcheck_p.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/cert_nonap_m10_11.txt
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/blockcheck_nonap.txt
---

Notation as in `fpbs-tree-projected-bidirectional-slot-second-moment-proof` (below: "the
bidirectional proof"). `L = {a^±1, b^±1}`, `x = 1/p`, `D_(t^-1) = -D_t`, `|D_t| = m`,
vertical part `{(1, ±c)}` with `c != 0`, `J = 1`, `K = 1`, runs `R = {-1, 0, 1}`. Only
the counting bound changes. The ensemble (section 1 there), the inclusion identity and
the symbolic block bounds (section 2), the refined nonzero capacity (section 3, Lemma 5),
the LP capacity map, Lemma 4 and the criterion of the vertical-slot proof are used
verbatim.

`engine_p.py` is `engine_r.py` of the bidirectional claim with the flags `POL` and
`NONAP` added. With both off it reproduces `engine_r`'s terms (1002 terms, `K = 1`).
(checked: identical exact matrices at `m = 10, 12`). With them on, the counting bound
depends on `m`: the engine compares strategies at
`M_REF = m`, so the terms are built once per `m`.

## 1. The counting problem

Fix a start class, a pair of slot structures, a set `Q` of shared-edge pairs and a
target class. As in the bidirectional proof, `N(Q)` counts assignments of the decoration
variables `V` (each `v` in its set `D_(dom v)`, `dom v in {t, o1, o2}`) that satisfy:
* a linear system `M` in `V`, `h`, `c` (the equations of `Q` and of the class);
* inequalities `v != v'` from the ensemble, always between variables of the same letter;
* the absence of internal coincidences (dropped: this only enlarges the count).

The three fibre letters `t`, `o1`, `o2` are distinct elements of `L`, so their sets are
three distinct members of `{D_a, -D_a, D_b, -D_b}`.

Choose a free set `F ⊆ V` such that the other variables `Det = V \ F` are determined by
`F`, `h` and `c` through `M` (`rank_cols(M, Det) = rank M`). `_express` writes each
`y in Det` as `y = Σ_(x in F) e_(y,x) x + alpha_y c + beta_y h` with rational
coefficients. A solution is determined by its values on `F`, so `N(Q)` is at most the
number of assignments of `F` that satisfy any chosen subset of the conditions
* `y in D_(dom y)` for `y in Det`;
* the inequalities between variables of `F`.

The bidirectional proof keeps the inequality forest on `F` and, for rigid decorations,
the conditions `y in D_y` of single-variable expressions (Lemma 6 there, gain
`m -> m-1` for the tree of `x`). Two further kinds of condition are used below.

## 2. Pollard pairs (flag `POL`)

**Lemma 7 (Pollard in Z).** Let `A, B, S` be finite subsets of `Q` with
`|A| = |B| = |S| = m`, and let `e1, e2` be nonzero rationals. Then
1. `#{(u, w) in A x B : e1 u + e2 w in S} <= P(m) := min_(0<=t<=m) [m t + (m-t)^2]`;
2. `#{(u, w) in A x A : u != w, e (u - w) in S} <= P_neq(m) := min_(0<=t<=m) [m t + (m-t)(m-t-1)]`
   for every nonzero rational `e`.

*Proof.* Put `A' = e1 A`, `B' = e2 B` and `r(s) = #{(u, w) in A' x B' : u + w = s}`,
so `Σ_s r(s) = m^2`. Pollard's theorem holds in `Z`: for finite `A', B' ⊂ Z` and
`1 <= t <= min(|A'|, |B'|)`,
`Σ_s min(t, r(s)) >= t(|A'| + |B'| - t)`. (It is proved for `Z/pZ` with `p` prime; a
finite configuration in `Z` embeds into `Z/pZ` for a prime `p` larger than twice the
diameter of `A' ∪ B'`, preserving all representation numbers. Rational sets are
scaled to integers first.) Hence, for `1 <= t <= m`,

```text
Σ_(s in S) r(s)  <=  Σ_(s in S) min(t, r(s)) + Σ_s (r(s) - t)^+
                 <=  m t + (m^2 - Σ_s min(t, r(s)))  <=  m t + m^2 - t(2m - t)  =  m t + (m-t)^2 .
```

`t = 0` gives the trivial `m^2`. This is part 1.

For part 2 take `A' = e A`, `B' = -e A`, so `r(0) = m` and the count is
`Σ_(s in S, s != 0) r(s)`, where the `m` diagonal pairs are exactly those with `s = 0`.
Now `Σ_(s != 0) r(s) = m^2 - m` and
`Σ_(s != 0) min(t, r(s)) >= t(2m - t) - t`. So, as above,
`Σ_(s in S \ 0) r(s) <= m t + (m^2 - m) - t(2m - t) + t = m t + (m-t)(m-t-1)`. ∎

**Lemma 8 (pair families).** In the setting of section 1, let `Π` be a family of
triples `(y_i, x1_i, x2_i)` with distinct `y_i in Det`, pairwise disjoint pairs
`{x1_i, x2_i} ⊆ F`, and `e_(y_i, x1_i), e_(y_i, x2_i) != 0`. Let `F' = F \ ∪ {x1_i, x2_i}`.
Suppose the pairs can be ordered so that the support of each `y_i` (the `x` with
`e_(y_i,x) != 0`) lies in `F'` together with its own pair and the earlier pairs. Let
`B(F')` be any valid bound for the number of assignments of `F'` alone (the forest
bound with the gains of Lemma 6 and Lemma 9, built only from inequalities inside `F'`
and from single-variable expressions `y` not among the `y_i`). Then

```text
N(Q)  <=  B(F') · Π_i P_i ,    P_i = P_neq(m) if x1_i, x2_i have the same letter,
                                        e_(y_i,x1_i) = -e_(y_i,x2_i) and x1_i != x2_i
                                        is an inequality of the ensemble;
                                  P_i = P(m) otherwise.
```

*Proof.* Count assignments of `F` in the given order: first `F'`, then the pairs one by
one. Keep only the conditions used by `B(F')` and the conditions `y_i in D_(y_i)`.
When the `i`-th pair is revealed, all other variables in the support of `y_i` are
already fixed, so `y_i in D_(y_i)` reads `e1 x1_i + e2 x2_i in D_(y_i) - const`. By
Lemma 7 (with the inequality `x1_i != x2_i` in the second case) this leaves at most
`P_i` choices, whatever the earlier values. ∎

`count_bound_pol` enumerates all free sets, all admissible families `Π` (distinct `y`,
disjoint pairs, order check by repeated covering), evaluates
`m^comps (m-1)^fedges P(m)^npl P_neq(m)^nnq (m-2)^g2` at `m = M_REF`, and keeps the
smallest. Every candidate is a valid upper bound by Lemma 8, so the minimum is too.
Inside the NZ refinement, the engine asserts that the new upper bound of each term is
still at least the exact `h' = 0` count subtracted by Lemma 5.

## 3. Non-AP collisions (flag `NONAP`; rigid decorations)

**Lemma 9.** Let `D ⊂ Z` be finite with `|D| = m >= 3`, and `gamma != 0`. If `D` is not
an arithmetic progression, then `|D ∩ (D - gamma)| <= m - 2`. A rigid set is not an
arithmetic progression.

*Proof.* Consider the graph on `D` with an edge `x -> x + gamma` whenever both lie in
`D`. It has `|D ∩ (D - gamma)|` edges. Since `gamma != 0` it has no cycle, and every
vertex has in- and out-degree at most 1, so it is a disjoint union of paths
(`gamma`-chains). A union of `k` paths on `m` vertices has `m - k` edges. So `m - 1`
edges means one chain, i.e. `D = {d, d + gamma, ..., d + (m-1) gamma}`, an arithmetic
progression. An arithmetic progression satisfies `-D = D + const`, so `D` and `-D` are
translates, which rigidity forbids. ∎

In the forest bound: if `y in Det` has `y = x + alpha c + beta h` with a single free
variable `x`, `dom x = dom y` and `gamma = alpha c + beta h` provably nonzero (the test
`_nonzero` of Lemma 6, cases 4), then `x` is confined to
`{x in D : x + gamma in D}` of size `<= m - 2`. The tree of `x` is rooted at `x` and
contributes `(m-2)(m-1)^(size-1)`. At most one gain is taken per tree, at the best level
over its candidates (`_forest_rig`). This is Lemma 6's argument with `m - 1` replaced by
`m - 2` in its case 4.

## 4. Certificate (`certify_p.py`, exact rationals)

As in section 5 of the bidirectional proof:
* `p_m = floor(10^6 p_low) / 10^6`, where `p_low < p*(m, 2)` uses `sqrt 3 < 17321/10000`
  and an integer square root rounded up;
* `T` and `w` are exact, with `K = 1` (4 classes), `R = {-1, 0, 1}`, flags `NZREF`,
  `RIGID`, `POL`, `NONAP`;
* `y` comes from float iteration of `Phi`, rounded to denominators at most `10^9`;
* `Phi(y) < 3 w^2 y` is checked in exact arithmetic.

| `m` | terms | `p_m` | `3w` | margin |
|---|---|---|---|---|
| 10 | 1154 | 28179/1000000 | 1.078089 | 4.716e-4 |
| 11 | 1154 | 25673/1000000 | 1.078572 | 6.589e-3 |

The certifying vectors are in `cert_nonap_m10_11.txt`:
* `m = 10`: `y = (82329796/538057379, 1, 82329796/538057379, 9004763/86497035)`;
* `m = 11`: `y = (30889158/218019583, 1, 30889158/218019583, 56241741/582310721)`.

**Consistency check (not part of the proof).** `blockcheck_p.py` runs the independent
C enumerator `pairx.c` on 7 rigid decorations for each `m in {8, 9, 10, 11}` (near-AP
families with `c = 1, 2, 5`, a second near-AP family, and three random rigid pairs). It
forms the exact class matrix `E[s][j] = sup_(h in s) Σ_(h' in j) Σ_k N(h, h', k) p^k`
and checks `E <= T` entrywise at `p = 0.07` and `p = 0.28/m`, with `T` the certified
`m`-specific bound. The largest ratio exact/bound is `0.9968` (near-AP, `m = 11`,
`p = 0.28/m`; `blockcheck_nonap.txt`). The one-block weight matches exactly in every
case.

## 5. Conclusion

For `m in {10, 11}` and every rigid decoration, `T` is an entrywise upper bound for the
class pair transfer (sections 1–3 and the bidirectional proof), `w` is a lower bound for
the one-block weight, and the certificate gives `rho(Phi) < 3 w^2` at `p_m`. The
criterion of the vertical-slot proof gives `p_c <= p_m`. Also
`p_m < p*(m, 2) <= p_{2->2} <= p_u` by
`fpbs-tree-projected-oriented-second-moment-thresholds`, whose hypotheses (rank `n = 2`,
uniform multiplicity `m`, `v = 2`) are met. ∎

## 6. Negative results (float, not part of the proof)

* The same certificate fails at `m = 9` (`rho/3w^2 = 1.0065`) and `m = 8` (`1.0151`).
* *Pointwise generic row (`PW`, `runpw.py`).* For generic start offsets `h`, a
  single-variable condition `y = s x + gamma` with `gamma = beta h + alpha c` confines `x`
  to exactly `R_kappa(h + j c)` values, where `R_kappa(g) = #{(u, w) in D_d1 x D_d2 :
  s1 u + s2 w = g}` depends on `h` only through `j = beta alpha`. Replacing the
  worst-case gain by the parameter makes the generic row affine in the vector
  `(R_kappa(h + j c))`, which ranges over the box given by the caps of Lemma 6 and
  Lemma 9. The excursion-free pairs with no shared edge land at `h' = k c` in exactly
  `R_((t,-1),(t,1))(h + (r2 - r1 - k) c)` ways, which is subtracted. `Phi_G` is then the
  supremum of an LP over the box, again an LP. Result: `1.0053` at `m = 9` (`1.0048`
  with `K = 2`), `0.9984` at `m = 10`. The supremum is attained with every cap active,
  so this is still lumping in `h`.
* *Where the loss sits at m = 9.* The certifying ratio is set by the `0` row. Its
  `0 -> 0` entry is `0.948`, of which `0.9277` is identity-type mass (exact for every
  decoration) and `0.0204` decoration-dependent, mostly energy-type pair counts `m ·
  P_neq(m)` and `R_t(±c)` terms. The generic class contributes `0.385 · y_G` with
  `y_G = 0.11`, and `y_G` is forced by the generic row's return mass to `0`.
* *Class lumping.* On the rigid near-AP family `A = {0..m-2, m}`,
  `B = {0..m-3, m-1, m}`, `c = 1`, at `m = 10` and `p = 0.02818`, the exact
  per-decoration transfer has `rho = 0.9745`, its class-lumped version `0.9890`. A
  generic-class test function `y(h) = a + b (r_A + r_B)(h)` (with `r_D(g) =
  #{(u, w) in D^2 : u - w = g}`) gives a Collatz–Wielandt bound `0.9768` on the same
  exact operator. So an `h`-dependent test function recovers about 80% of the lumping
  loss. A heights-uniform version needs a bound for the weighted landing mass
  `Σ_(h' in G) T(s, h') (r_A + r_B)(h')`, which is again a counting problem with two
  extra variables `u - w = h'` (flag `WAUG`, `runwa.py`). At `m = 9` that count gives
  `W/3w^2 <= 4.68, 6.44, 4.68` from `-c, 0, c` and `4.46` uniformly from `G`. The
  uniform generic bound kills the gain: at `h` with `S(h) = 0` the generic row needs
  `a (lam - T_GG) >= b W(h)`, so the optimal `b` is `0` and `rho` stays `1.00532`
  (`runwa2.py`). The true `W(h)` vanishes for `h` far from `D - D`; a pointwise bound in
  terms of higher-order autocorrelations at `h` is needed.
