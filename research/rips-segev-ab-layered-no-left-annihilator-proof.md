---
rg: 2
id: rips-segev-ab-layered-no-left-annihilator-proof
kind: route
title: For alpha (sum_j u_j b^j) = 0 the active points of each b-line form clusters with gaps at most d; the b-edges inside cluster spans form a port graph of minimum degree 2 whose leaf-block flow cycle has, in each copy, at most one pure active untouched line and pairwise non-consecutive inactive ones, so visits of 3 to 8 cosets close into a relation that Greendlinger forbids; a coset-wise gcd flip reduces left annihilators of u + v b w to those of u_0 + w_0 v b
target: rips-segev-ab-layered-elements-have-no-left-annihilator
requires: [rips-segev-two-layer-elements-have-no-left-annihilator, rips-segev-two-layer-cycles-split-over-copies, rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-two-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors, rips-segev-steenbock-few-line-a-supports-are-regular]
---

**Conventions.**
- [NL] is `rips-segev-two-layer-no-left-annihilator-proof`: Lemma 1 (cycle graphs), the visit construction, and
  the Greendlinger step of its §1, and the flow lift of its §2 Step 3.
- [SP] is `rips-segev-two-layer-cycles-split-over-copies-proof`: Step 0 (from `G` to `K`), Step 2 (splitting),
  Step 3 (cycle lines), and the row sets `D_r` with `(D_r - D_r) ∩ (D_r' - D_r') = {0}` for `r != r'`.
- [3C] is `rips-segev-three-copy-no-zero-divisors-proof` (Lemma 1, the rank-one lemma, reproved below for many
  layers).  [2C] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof` (Corollary 3: distinct
  copies meet at most 3 common cosets).  [1C] is `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`
  (a coset meets a copy in at most one line).
- [FL] is `rips-segev-steenbock-few-line-a-supports-are-regular-proof`: the gluing table of its §1 and Lemma A.
- `Cay`, copies `C = h g(Gamma)`, the coset graph `Q`, cycle lines, touched and untouched cosets are as in [NL].
- Positions on a line of `Gamma` are `0 < I_1 < I_2 < O_1 < O_2 < C`.  A position is a *middle* if it is both
  the target and the source of a `b`-edge of `Gamma`.  By the table of [FL] §1 the middles are `0` and `C`.

**Fact M (neighbours of middles).**  Let `x -> p -> y` be the two `b`-edges of `Gamma` at a middle `p`.  Then
neither `x` nor `y` is a middle.
- *Proof.*  By [FL] Lemma A(b) there is no path of three `b`-edges of one orientation.  If `x` were a middle,
  the edge into `x` followed by `x -> p -> y` would be one.  The same holds for `y`. ∎
- Concretely, `x` is at an `O` position and `y` at an `I` position.

## 1. The flip (Theorem B)

Let `H` be any group and `a in H` of infinite order.  Identify `k[<a>]` with `k[t^{±1}]`.
- For a left coset `T = z_T <a>` and `gamma in k[H]`, write `gamma|_T = z_T gamma_T(a)` with
  `gamma_T in k[t^{±1}]`.
- For `p in k[<a>]`, `(gamma p)|_T = z_T gamma_T(a) p(a)`, since right multiplication by `a` preserves `T`.
  So `(gamma p)_T = gamma_T p`.
- In particular right multiplication by a nonzero `p in k[<a>]` is injective on `k[H]`, because `k[t^{±1}]` is a
  domain.

**Lemma F.**  Let `u, v, w in k[<a>]` with `v != 0` and `w != 0`, let `c in H`, and let `alpha (u + v c w) = 0`.
1. If `u = 0`, then `alpha = 0`.
2. Otherwise let `g = gcd(u, w)` in `k[t^{±1}]`, with `u = g u_0` and `w = g w_0`.  There is `eta in k[H]` with
   `alpha = eta w_0` and `eta (u_0 + w_0 v c) = 0`.  If `alpha != 0` then `eta != 0`.

*Proof.*
1. `alpha v c w = 0`.  Right multiplication by `w`, by the unit `c` and by `v` is injective, so `alpha = 0`.
2. Put `gamma = alpha v c`.  Then `alpha u = -gamma w`, that is `(alpha u_0 + gamma w_0) g = 0`.  Cancel `g`:
   `alpha u_0 = -gamma w_0`.
   - Coset by coset: `alpha_T u_0 = -gamma_T w_0` in `k[t^{±1}]`.
   - `k[t^{±1}]` is a UFD and `gcd(u_0, w_0) = 1`.  So `w_0` divides `alpha_T`.  Write `alpha_T = w_0 h_T`; then
     `gamma_T = -u_0 h_T`.  Only finitely many `h_T` are nonzero.
   - Put `eta = sum_T z_T h_T(a)`.  Then `alpha = eta w_0` and `gamma = -eta u_0`.
   - So `eta w_0 v c = alpha v c = gamma = -eta u_0`, that is `eta (u_0 + w_0 v c) = 0`.
   - `alpha = eta w_0` with `alpha != 0` forces `eta != 0`. ∎

Theorem B is Lemma F with `c = b^eps`.

**Calibration of Lemma F.**  In `H_{m,n} = <a, b | (a^m b)^n>`, `n >= 3`, put `x = a^m b` and
`alpha = sum_{j<n} x^j`.
- `(1 - x) alpha = 0`, so `alpha^* (1 - b^{-1} a^{-m}) = 0`.  This is Lemma F with `u = 1`, `v = 1`, `c = b^{-1}`,
  `w = -a^{-m}`, so `g = 1`, `u_0 = 1`, `w_0 = -a^{-m}`.
- The lemma predicts `eta = -alpha^* a^m` and `eta (1 - a^{-m} b^{-1}) = 0`.
- Check: `alpha^* = alpha^* b^{-1} a^{-m}`, so `alpha^* a^m = alpha^* b^{-1}`.  Hence
  `eta (1 - a^{-m} b^{-1}) = -alpha^* a^m + alpha^* b^{-1} = 0`.

## 2. Setting of Theorem A

Let `beta = sum_{j=0}^d u_j b^j` and `alpha beta = 0` with `alpha != 0`.
- *Normalization.*  Right multiplication by `b^{-m}` shifts the layers, so we may assume `u_0 != 0` and
  `u_d != 0`.  If `d = 0`, then `alpha u_0 = 0` gives `alpha = 0` (§1).  So `d >= 1`.
- *Core.*  By [SP] Step 0, which only uses that `supp beta ⊆ K`, we may take `alpha in k[K]`.
- *Infinite field.*  Replace `k` by `k(s)`.  Every lemma cited holds over every field, so `k` is infinite.
- *Layers.*  Put `X_j = alpha u_j in k[K]`.  On a coset `T`, `X_j|_T = z_T P^j_T(a)` with `P^j_T = f_T u_j`, where
  `alpha|_T = z_T f_T(a)`.  `T` is *active* if `f_T != 0`.  Then `P^0_T != 0` and `P^d_T != 0`.
- A point `x` is *active* if `X_j(x) != 0` for some `j`.  A coset is active iff it contains an active point.
- *The equation.*  `(alpha beta)(v) = sum_j (X_j b^j)(v) = sum_j X_j(v b^{-j}) = 0` for every `v in K`.

## 3. Clusters and the port graph

Fix a `b`-line `L = y <b>` and write `x_n = y b^n`.  Put `A_L = {n : x_n active}`, a finite set.
- A *cluster* is a maximal subset `{n_1 < ... < n_s}` of `A_L` with `n_{r+1} - n_r <= d` for all `r`.  Its
  *span* is the set of `b`-edges `[x_n -> x_{n+1}]` with `n_1 <= n < n_s`.
- Distinct clusters of `L` are more than `d` apart, and their spans are disjoint.

**Lemma 1 (cluster ends).**  Let `{n_1 < ... < n_s}` be a cluster.
1. `X_0(x_{n_1}) = 0` and `X_d(x_{n_s}) = 0`.
2. `s >= 2`.

*Proof.*  The positions `n_1 - d, ..., n_1 - 1` and `n_s + 1, ..., n_s + d` are inactive.
1. The equation at `v = x_{n_1}` reads `sum_j X_j(x_{n_1 - j}) = 0`.  Every term with `j >= 1` is at an inactive
   point, so `X_0(x_{n_1}) = 0`.  The equation at `v = x_{n_s + d}` leaves only `X_d(x_{n_s})`.
2. If `s = 1`, put `n = n_1`.  For each `j`, the equation at `v = x_{n+j}` involves the points `x_{n+j-i}`,
   `0 <= i <= d`.  All of them except `x_n` (for `i = j`) are inactive.  So `X_j(x_n) = 0` for every `j`, and
   `x_n` is not active. ∎

**The port graph.**  `S ⊆ Q` has one edge for each `b`-edge of `Cay` lying in the span of a cluster.  Its
vertices are the end cosets of its edges.

**Lemma 2 (degrees).**
1. Every active point `x` lies on an edge of `S`.
2. Every inactive point `p` on an edge of `S` lies on exactly two: `[p b^{-1} -> p]` and `[p -> p b]`.
3. Every vertex of `S` has degree `>= 2`.

*Proof.*
1. `x` lies in a cluster, which has `s >= 2` points, so an edge of its span ends at `x`.
2. An inactive point is not a cluster point, so it is strictly inside a span, and both `b`-edges at it lie in
   that span.
3. Let `T` be a vertex.
   - If `T` is active, pick `x in T` with `X_0(x) != 0`.  By Lemma 1.1, `x` is not the least point of its
     cluster, so `[x b^{-1} -> x] in S`.  Pick `y in T` with `X_d(y) != 0`.  By Lemma 1.1, `[y -> y b] in S`.
     These are distinct: equality would give `y b = x`, so `b in <a>`.
   - If `T` is inactive, it contains an inactive point on an edge of `S`, and Lemma 2.2 gives two edges.
   - Distinct `b`-edges of `Cay` are distinct edges of `Q`, and `Q` has no loops ([2C] Lemma 6: `b a^n` is not a
     relation). ∎

## 4. The flow cycle and the two kinds of good lines

**Step 1 (flow cycle).**  Exactly as in [NL] §2 Steps 2–3, which use only that `S` is a finite graph of minimum
degree 2 and that `k` is infinite:
- take a leaf 2-edge-connected block `B` of a component of `S`, with bridge end `T_B` (undefined if the
  component is 2-edge-connected); a vertex `T != T_B` of `B` is *good*, and every edge of `S` at a good vertex
  lies in `B`;
- a nowhere-zero `k`-flow on `B` lifts to a finite nonzero cycle `c` on `Cay` whose `b`-support is exactly
  `E(B)`; the lift adds an `a`-chain on every coset of `V(B)`, active or not, since conservation holds at every
  vertex;
- by [SP] Step 2, `c = sum_{i <= N} c_i` with distinct copies `C_i` and `0 != c_i in Z_1(C_i; k)`.

Let `l` be an untouched cycle line of `C_i`, in the coset `T`.  As in [NL] Step 4:
- `c_i` is nonzero on a `b`-edge `e` of `C_i` at `l`, and `c(e) = c_i(e)`, so `e in E(B)` and `T in V(B)`;
- on every edge with an endpoint in `T`, `c = c_i`.

**Lemma 3 (the edges at a good untouched line).**  Let `l` be as above, with `T` good.  Every edge of `S` at
`T` is a `b`-edge of `C_i` with an endpoint on `l`.

*Proof.*  Such an edge lies in `B` since `T` is good, so `c` is nonzero on it.  Then `c_i` is nonzero on it,
so it is a `b`-edge of `C_i`.  Its endpoint in `T` is a vertex of `C_i` in `T`, hence on `l` by [1C]. ∎

**Lemma 4 (pure active lines).**  If moreover `T` is active, then, with the start of `l` as base point,
`S_T = union_j supp P^j_T ⊆ In_l ∪ Out_l ⊆ D_r`, where `r` is the row of `l`.

*Proof.*  An active point `x in T` lies on an edge of `S` (Lemma 2.1).  By Lemma 3, `x in l`, and `x` is an
endpoint of a `b`-edge of `C_i`.  So the position of `x` lies in `In_l ∪ Out_l`.  The inclusion in `D_r` is
[SP] Step 4. ∎

**Lemma 5 (inactive lines are isolated).**  Let `l`, `l'` be untouched cycle lines of the same copy `C_i`, in
good inactive cosets `T`, `T'`.  Then no edge of `Lambda_i` joins `T` and `T'`.

*Proof.*  Suppose `e` is an edge of `Lambda_i` from `T` to `T'`.  It is a `b`-edge of `C_i`, and `c_i(e) != 0`.
- As `T` is untouched, `c(e) = c_i(e) != 0`, so `e in E(B) ⊆ E(S)`.
- Let `p in T` and `q in T'` be its endpoints.  They are inactive points on an edge of `S`, so by Lemma 2.2 both
  `b`-edges at `p` and both `b`-edges at `q` lie in `S`.
- By Lemma 3, applied at `T` and at `T'`, all four are `b`-edges of `C_i`.  So `p` and `q` are both targets
  and sources of `b`-edges of the embedded copy `C_i`, that is, both are middles.
- But `e` joins `p` and `q` by one `b`-edge.  That contradicts Fact M. ∎

**Lemma 6 (at most one pure line per copy).**  No copy `C_i` has two untouched cycle lines in good active
cosets.

*Proof.*  Two such lines lie in distinct cosets ([SP] Step 3) and have distinct rows (`phi` is injective).
By Lemma 4 and `(D_r - D_r) ∩ (D_r' - D_r') = {0}`, Lemma 7 below gives `alpha = 0`. ∎

## 5. The rank-one lemma for many layers

**Lemma 7.**  Let `H` be a group, `a, b in H` of infinite order, `alpha in k[H]`, and `u_0, ..., u_d in k[<a>]`
not all zero, with `alpha (sum_j u_j b^j) = 0`.  Let `T != T'` be left `<a>`-cosets with `f_T != 0 != f_T'`, and
put `S_T = union_j supp(f_T u_j)`.  If `(S_T - S_T) ∩ (S_T' - S_T') = {0}`, then `alpha = 0`.

*Proof.*
- *Injectivity.*  As in [3C] Lemma 1, `(x, y) -> x + y` is injective on `S_T × S_T'`.
- *Tensor identity.*  For all `i, j`, `P^i_T P^j_T' = f_T f_T' u_i u_j = P^i_T' P^j_T`.  All factors are
  supported in `S_T` or `S_T'`.  By injectivity, comparing the coefficients of `t^{x+y}` gives
  `P^i_T(x) P^j_T'(y) = P^i_T'(y) P^j_T(x)` for all `x in S_T`, `y in S_T'`.
- *Rank one.*  Some `u_{i_0} != 0`, so `P^{i_0}_T' = f_T' u_{i_0} != 0`.  Pick `y_0` with
  `P^{i_0}_T'(y_0) != 0` and put `c_j = P^j_T'(y_0) / P^{i_0}_T'(y_0)`.  With `i = i_0`, `y = y_0`:
  `P^j_T(x) = c_j P^{i_0}_T(x)` for all `x`.  So `f_T u_j = c_j f_T u_{i_0}`, and `u_j = c_j u_{i_0}` as
  `f_T != 0`.
- *Conclusion.*  Then `beta = u_{i_0} q(b)` with `q(s) = sum_j c_j s^j != 0` (`c_{i_0} = 1`).  Put
  `alpha' = alpha u_{i_0}`, so `alpha' q(b) = 0`.
  - Decompose `alpha'` along left `<b>`-cosets: on each, the piece `g(s)` satisfies `g q = 0` in the domain
    `k[s^{±1}]`, so `g = 0`.  Hence `alpha' = 0`.
  - Right multiplication by `u_{i_0} != 0` is injective (§1), so `alpha = 0`. ∎

For `d = 1` this is [3C] Lemma 1.

## 6. Hopping with windows of six

**Lemma 8 (touched cosets come early).**  Assume no `C_i` has two untouched cycle lines in good active cosets
(Lemma 6).  Let `v_0, v_1, ..., v_8` be a non-backtracking walk in `Lambda_i`.  Then one of `v_3, ..., v_8` is
touched for `C_i`.

*Proof.*  The cosets `v_3, ..., v_8` are six distinct cosets ([NL] Lemma 1.1, as `8 <= 41`), and each is a cycle
line of `C_i` ([NL] Lemma 1.2).  Suppose all six are untouched.
- At most one is `T_B`, and by Lemma 6 at most one is good and active.  So at least four are good and
  inactive.
- Consecutive `v_t, v_{t+1}` are joined by an edge of `Lambda_i`.  By Lemma 5 no two of the good inactive
  ones are consecutive.
- Four pairwise non-consecutive terms among six consecutive terms of a sequence would need at least seven
  terms.  This is a contradiction. ∎

**Proposition 9.**  Under the assumption of Lemma 8, the splitting `c = sum_{i <= N} c_i` cannot exist.

*Proof.*  Run the visit construction of [NL] §1 with the walk `v_0, ..., v_8` in place of `v_0, ..., v_5`.
- A visit from the state `(i, v, e)` follows the least non-backtracking walk in `Lambda_i` and stops at the
  first touched coset among `v_3, ..., v_8`, which exists by Lemma 8.  So each visit has `3` to `8` edges.
- The rest of [NL] §1 is unchanged: the states cycle, the concatenated visits form a cyclically
  non-backtracking closed walk `ell` in `Q` with `p >= 2` visits, consecutive visits lie in distinct copies,
  and its lift is a cyclically reduced relation `W != 1` of `K`.
- *Greendlinger.*  As in [NL] §1, a minimal diagram for `W` either has one face, so all of `ell` lies in one
  copy `C_M`, or it has a face `M` with an exterior arc reading at least 13 cyclically consecutive edges of
  `ell`, all edges of `C_M`.
- *Four cosets pin a copy* ([NL] §1, from [2C] Corollary 3).  If three consecutive edges of a visit in
  `Lambda_i` are edges of `C_M`, then `C_i = C_M`.
- *Counting.*  In the one-face case apply this to the first three edges of two consecutive visits.  Otherwise
  take the 13 edges, and let the first `j >= 1` of them be the last `j` edges of the visit `A`.
  - If `j >= 3`, the three edges before position `j + 1` lie in `A`, and the next `min(|A'|, 13 - j) >= 3`
    edges start the next visit `A'`, since `13 - j >= 13 - 8 = 5`.
  - If `j <= 2`, the next visit `A'` lies entirely among the 13 (`j + |A'| <= 10`), and the next
    `13 - j - |A'| >= 3` edges start the visit `A''` after `A'`.  Here `A'' = A` is allowed when `p = 2`.
  - Either way two consecutive visits, in distinct copies, each have three consecutive edges in `C_M`.  Both
    copies equal `C_M`, which is a contradiction. ∎

## 7. Proof of Theorem A and Corollary C

*Theorem A.*  With `alpha != 0`, §2–§4 give the splitting.  Lemma 6 holds, since otherwise Lemma 7 gives
`alpha = 0`.  Then Proposition 9 is a contradiction.  So `alpha = 0`.
- The passage from `k[G]` to `k[K]` and to `k(s)` is §2.
- For supports in `<b><a>` apply the involution: `(sum_j b^j v_j) gamma = 0` gives
  `gamma^* (sum_j v_j^* b^{-j}) = 0`, which Theorem A excludes. ∎

*Corollary C.*  Let `x = u + v b^eps w` with `v w != 0`.
- *Left.*  Let `alpha x = 0`.  If `u = 0` then `alpha = 0` by Lemma F.1.  Otherwise Lemma F.2 gives
  `eta (u_0 + w_0 v b^eps) = 0`.  For `eps = 1` this is Theorem A with `d = 1`.  For `eps = -1`,
  `(u_0 + w_0 v b^{-1}) b = w_0 v + u_0 b`, so `eta (w_0 v + u_0 b) = 0` and Theorem A applies again, since
  `w_0 v != 0`.  So `eta = 0` and `alpha = eta w_0 = 0`.
- *Right.*  Let `x gamma = 0`.  Then `gamma^* x^* = 0` with `x^* = u^* + w^* b^{-eps} v^*`, which is of the same
  form with `w^* v^* != 0`.  The left case gives `gamma^* = 0`. ∎

## 8. Checks and what is open

- *`d = 1`.*  Gaps are `1`, and `S` contains every edge `[y -> y b]` with `X_1(y) != 0`, the port graph of [NL].  Lemma 5
  is not needed there: for `d = 1` a span has no interior inactive point, so every vertex of `S` is active.
- *Where Steenbock's gluing enters.*  Rows (Lemmas 4, 6, 7) as before, and Fact M (Lemma 5), which uses that
  `b`-runs have at most two edges.  In a graph with `b`-runs of length 3, two consecutive pass-through lines
  would be possible and the window count of Lemma 8 would fail.
- *Calibration.*  In `H_{m,n}` the zero divisor `alpha (1 - a^m b) = 0` passes §3–§4 (one cluster per
  `b`-edge of the relator loop, every coset active), and fails exactly at Lemma 6: all lines have the port
  set `{0, m}`, so Lemma 7 does not apply.
- *Right annihilators of `b`-degree `>= 2`* (left annihilators of `sum_j b^j v_j`).  Put
  `alpha_{T,j}(n) = alpha(z_T a^n b^{-j})`.  The equation is `sum_j v_j alpha_{T,j} = 0` on every coset.
  - Each `y in supp alpha` gives a segment `y, y b, ..., y b^d`, and the segment edges form a port graph of
    minimum degree 2.  The flow cycle and Lemma 3 transfer, so good untouched active lines are pure, with
    `alpha_{T,0}` in `Out_l`, `alpha_{T,d}` in `In_l`, and middle levels at `{0, C}`.
  - The port vector `(alpha_{T,j})_j` lies in the syzygy module of `(v_0, ..., v_d)`, which has rank `d`.  For
    `d = 1` it is `h_T (v_1', -v_0')`, rank one, and this is the flip.  For `d >= 2` there is no tensor
    identity between two cosets, so Lemma 7 has no analogue.
  - A single pure coset of row `r` still forces `(D_r - D_r) ∩ (M - M) != {0}` for `M = union_j supp v_j` (top
    degree cancellation), when the `v_j` are `k`-independent.  This bounds the pure lines per copy by the
    number of such rows, not by one.
