---
rg: 2
id: rips-segev-rank-two-ba-no-left-annihilator-proof
kind: route
title: For alpha (sum_j b^j v_j) = 0 the segments y..y b^d give a port graph of minimum degree 2 and the leaf-block flow cycle; good untouched lines are middle lines, never consecutive by Fact M, or bad lines whose port polynomials are multiples of v_0 or v_d; a determinant over distinct rows plus Rado's theorem puts the bad lines in at most dim span(v_j) - 1 rows, one when that span has dimension 2, and the window-of-6 Greendlinger argument closes
target: rips-segev-rank-two-ba-elements-have-no-left-annihilator
requires: [rips-segev-ab-layered-elements-have-no-left-annihilator, rips-segev-two-layer-elements-have-no-left-annihilator, rips-segev-two-layer-cycles-split-over-copies, rips-segev-two-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors, rips-segev-steenbock-few-line-a-supports-are-regular]
---

**Conventions.**
- [AB] is `rips-segev-ab-layered-no-left-annihilator-proof`: Fact M, §4 Step 1 (the flow cycle), and
  Lemma 8 and Proposition 9 (windows of six, visits, Greendlinger).
- [NL] is `rips-segev-two-layer-no-left-annihilator-proof` (Lemma 1, cycle graphs `Lambda_i`, touched cosets).
- [SP] is `rips-segev-two-layer-cycles-split-over-copies-proof` (Step 0, Step 2 splitting, Step 3 cycle
  lines).  [1C] is `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof` (a coset meets a copy in at
  most one line).  [2C] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof`.
- [FL] is `rips-segev-steenbock-few-line-a-supports-are-regular-proof` (§1 gluing table, Lemma A).
- Positions on a line of `Gamma` are `0 < I_1 < I_2 < O_1 < O_2 < C`, equal to
  `0, 10^{5r-4}, ..., 10^{5r}` for the row `r`.  By [FL] §1 the *sources* of `b`-edges are at `0, O_1, O_2, C`
  and the *targets* at `0, I_1, I_2, C`.  The *middles* (both) are `0` and `C`.

## 1. Setting

Let `beta = sum_{j=0}^d b^j v_j` with `v_j in k[<a>] = k[t^{±1}]`, and `alpha beta = 0` with `alpha != 0`.
- *Normalization.*  `alpha beta = 0` iff `(alpha b^m)(b^{-m} beta) = 0`, and `alpha b^m != 0`.  So we may assume
  `v_0 != 0 != v_d`.  If `d = 0`, then `alpha v_0 = 0` and `alpha = 0` ([AB] §1).  So `d >= 1`.
- *Core.*  `supp beta ⊆ K`, so by [SP] Step 0 we may take `alpha in k[K]`.
- *Infinite field.*  Replace `k` by `k(s)`; nothing below depends on the field.
- *Levels.*  For `x in K` put `L(x) = {j in [0, d] : x b^{-j} in supp alpha}`.  `x` is *covered* if
  `L(x) != ∅`.
- *Coset data.*  For `T = z_T <a>` put `p_{T,j}(n) = alpha(z_T a^n b^{-j})`, a Laurent polynomial.
- *The equation.*  For `g = z_T a^N`,
  `(alpha beta)(g) = sum_j sum_m v_j(m) alpha(g a^{-m} b^{-j})`, which is the coefficient of `t^N` in
  `sum_j p_{T,j} v_j`.  So `sum_j p_{T,j} v_j = 0` in `k[t^{±1}]` for every coset `T`.
- *Port polynomials.*  For `x = z_T a^N` put `p_T(x) = (p_{T,j}(N))_j in k^{d+1}` and
  `g_x = sum_j p_{T,j}(N) v_j in V := span_k(v_0, ..., v_d)`.  Then `sum_N t^N g_{z_T a^N} = 0`.
- Put `n = dim_k V`.  Then `n >= 1`.

## 2. The port graph

`S` is the subgraph of the coset graph `Q` ([NL]) formed by the `b`-edges `[y b^j -> y b^{j+1}]`, for
`y in supp alpha` and `0 <= j < d`, and their end cosets.
- `[x -> x b] in S` iff `L(x)` meets `[0, d-1]`, iff `L(x b)` meets `[1, d]`.
- So every covered point lies on an edge of `S`: level `j < d` gives the out-edge, level `j >= 1` the in-edge.
  Conversely every endpoint of an edge of `S` is covered.

**Lemma 1 (degrees).**  Every vertex of `S` has degree `>= 2`.

*Proof.*  Let `T` be a vertex; it contains a covered point.
- If some covered `x in T` has a level `0 < j < d`, both `[x b^{-1} -> x]` and `[x -> x b]` lie in `S`.
- If some covered `x` has `{0, d} ⊆ L(x)`, the same holds.
- Otherwise every covered point of `T` has `L(x) = {0}` or `L(x) = {d}`.  Then `p_{T,j} = 0` for `0 < j < d`, so
  `p_{T,0} v_0 + p_{T,d} v_d = 0`.  Some `p_{T,0}` or `p_{T,d}` is nonzero, and `k[t^{±1}]` is a domain, so both
  are.  A point with level `0` gives an out-edge, and a point with level `d` gives an in-edge.
- In each case the two `b`-edges of `Cay` are distinct.  In the last case equality would give `x b = x'` with
  `x, x' in T`, so `b in <a>`.  Distinct `b`-edges of `Cay` are distinct edges of `Q`, and `Q` has no loops
  ([2C] Lemma 6). ∎

## 3. Flow cycle and purity

**Step 1.**  [AB] §4 Step 1 uses only that `S` is a finite graph of minimum degree 2 and that `k` is infinite.
It gives:
- a leaf 2-edge-connected block `B` with bridge end `T_B` (possibly undefined); a vertex `T != T_B` of `B` is
  *good*, and every edge of `S` at a good vertex lies in `B`;
- a finite nonzero cycle `c` on `Cay`, nonzero exactly on the `b`-edges `E(B)` among `b`-edges;
- the splitting `c = sum_{i <= N} c_i` into distinct copies `C_i`, with cycle lines and cycle graphs `Lambda_i`
  as in [NL] Lemma 1.

**Lemma 2 (edges at a good untouched line).**  Let `l` be an untouched cycle line of `C_i` in a coset `T`.
1. `T in V(B)`.
2. If `T` is good, the edges of `S` at `T` are exactly the edges of `Lambda_i` at `T`, and each is a `b`-edge of
   `C_i` with an endpoint on `l`.

*Proof.*
1. `c_i` is nonzero on some `b`-edge `e` of `C_i` at `l`.  As `T` is untouched, `c(e) = c_i(e) != 0`, so
   `e in E(B)`.
2. An edge of `S` at `T` lies in `B`, so `c` is nonzero on it.  Since `T` is untouched, `c = c_i` there.  So it is
   a `b`-edge of `supp c_i`, an edge of `Lambda_i`, and its endpoint in `T` lies on `l` by [1C].  Conversely an
   edge of `Lambda_i` at `T` has `c = c_i != 0`, so it lies in `E(B) ⊆ E(S)`. ∎

**Lemma 3 (purity).**  Let `T` be good, with an untouched cycle line `l` of row `r`, based at the start of `l`.
Every covered point `x in T` lies on `l`, at a position in `D_r`, and:
- at `I_1, I_2` (targets only), `L(x) = {d}`, so `g_x = alpha(x b^{-d}) v_d`;
- at `O_1, O_2` (sources only), `L(x) = {0}`, so `g_x = alpha(x) v_0`;
- at `0, C` any levels occur.

*Proof.*  `x` lies on an edge of `S` (§2).  By Lemma 2 it lies on `l`, and each edge of `S` at `x` is a `b`-edge
of `C_i` at `x`.  A level `j < d` needs the out-edge, so the position of `x` is a source; a level `j >= 1` needs
the in-edge, so it is a target. ∎

**Definition.**  A good untouched cycle line is a *middle line* if all covered points of its coset sit at `0`
or `C`, and a *bad line* otherwise.
- A bad line has a covered point at an `I` or `O` position.  By Lemma 3 its port polynomial there is a nonzero
  multiple of `v_d` or `v_0`, hence nonzero.

**Lemma 4 (middle lines are isolated).**  Two middle lines of `C_i` are not joined by an edge of `Lambda_i`.

*Proof.*  Let `e` be such an edge, with endpoints `p in T` and `q in T'`.  By Lemma 2, `e in S`, so `p` and `q`
are covered.  So both sit at `0` or `C` of their lines, which are middles of the embedded copy `C_i`.  But `e`
is a `b`-edge of `C_i` joining them, against Fact M ([AB]). ∎

## 4. The row bound

Fix a basis `w_1, ..., w_n` of `V`.  For a subspace `W ⊆ k^n` let `ev : k^n -> V` send `c` to `sum_l c_l w_l`;
it is a `k`-isomorphism.  Extend it to `k[t^{±1}]^n -> k[t^{±1}]`, `f -> sum_l f_l w_l`.
- For a coset `T` let `c_T(x) in k^n` be the coordinate vector of `g_x`, and `f_T = sum_N t^N c_T(z_T a^N)`.
  §1 says `ev(f_T) = 0`.  Also `c_T(x) != 0` only at covered points `x`.
- Put `U_T = span_k {c_T(x) : x in T}`.
- `T` is *pure of row `r`* if its covered points lie in `z_T a^{N_T + D_r}` for some `N_T`.  Then
  `f_T = t^{N_T} sum_{e in D_r} t^e c_T(z_T a^{N_T + e})`.

**Lemma 5 (sums over distinct rows).**  Let `r_1 < ... < r_m` be rows.  Then `(e_1, ..., e_m) -> sum_k e_k` is
injective on `D_{r_1} × ... × D_{r_m}`.

*Proof.*  Let `e != e'` have equal sums, and `k` be the largest index with `e_k != e'_k`.
- Nonzero elements of `D_r - D_r` have absolute value at least `10^{5r-4}`.
- `|sum_{k' < k} (e_{k'} - e'_{k'})| <= sum_{r' < r_k} 10^{5r'} < 2 * 10^{5 r_k - 5} < 10^{5 r_k - 4}`.
- So `e_k - e'_k = -sum_{k'<k} (e_{k'} - e'_{k'})` is impossible. ∎

**Lemma 6 (row bound).**  Let `W ⊆ k^n` have dimension `w >= 1`, and let `T_1, ..., T_m` be cosets, pure of
pairwise distinct rows, with `0 != U_{T_k} ⊆ W`.  Then `m <= w - 1`.

*Proof.*  Induction on `w`.  Write `U_k = U_{T_k}`, `f_k = f_{T_k}`, `c_k = c_{T_k}`.
- *`w = 1`.*  `W = k u` with `ev(u) != 0`, and `f_k = h_k u` with `h_k != 0`.  Then
  `0 = ev(f_k) = h_k ev(u)` in the domain `k[t^{±1}]`, a contradiction.  So `m = 0`.
- *Step.*  Let `w >= 2` and suppose `m >= w`; keep `T_1, ..., T_w`.  Choose a basis of `W` and write the `f_k`
  in its coordinates as columns of a `w × w` matrix `F` over `k[t^{±1}]`.
  - The basis maps under `ev` to `k`-independent elements of `k[t^{±1}]`, so the syzygies of `W` form a
    module of rank `w - 1`.  All `w` columns are syzygies, so `det F = 0`.
  - By multilinearity, `det F = t^{sum N_k} sum_e t^{sum e_k} det[c_1(x_1(e_1)), ..., c_w(x_w(e_w))]` over
    `e in D_{r_1} × ... × D_{r_w}`, with `x_k(e) = z_{T_k} a^{N_k + e}`.  By Lemma 5 the exponents are distinct,
    so every such determinant vanishes.
  - So no choice of one vector from each spanning set `{c_k(x)}` is a basis of `W`.  By Rado's theorem (the
    linear-matroid form of Hall's theorem) some `J ⊆ [w]` has `w' := dim sum_{k in J} U_k < |J|`.
  - `1 <= w' < |J| <= w`.  The cosets `T_k`, `k in J`, satisfy the hypotheses for `W' = sum_J U_k`, so
    `|J| <= w' - 1` by induction.  This contradicts `w' < |J|`. ∎

**Corollary 7 (bad lines per copy).**  A copy `C_i` has at most `n - 1` bad lines.  For `n <= 2` it has at most
one.

*Proof.*  A bad line `l` of row `r` lies in a good coset `T` with an untouched cycle line, so `T` is pure of row
`r` by Lemma 3, and `U_T != 0` by the definition.  Lines of one copy have pairwise distinct rows (`phi` is
injective).  Apply Lemma 6 with `W = k^n`. ∎

- For `n = 2` and two cosets, Lemma 6 is the rank-one step of [AB] Lemma 7: the two syzygies are proportional.

## 5. Windows and the proof of Theorem R

**Lemma 8 (touched cosets come early).**  Assume every copy has at most one bad line (Corollary 7, `n <= 2`).
Let `v_0, ..., v_8` be a non-backtracking walk in `Lambda_i`.  Then one of `v_3, ..., v_8` is touched for `C_i`.

*Proof.*  As in [AB] Lemma 8, `v_3, ..., v_8` are six distinct cosets, each a cycle line of `C_i`.  Suppose all
six are untouched.
- At most one is `T_B`.  The others are good, so each is a middle line or a bad line, and at most one is bad.
  So at least four are middle lines.
- Consecutive terms are joined by an edge of `Lambda_i`, so by Lemma 4 no two middle lines are consecutive.
- Four pairwise non-consecutive terms need at least seven consecutive terms.  Contradiction. ∎

**Proposition 9.**  Under the assumption of Lemma 8 the splitting of Step 1 cannot exist.

*Proof.*  The proof of [AB] Proposition 9 uses only the conclusion of [AB] Lemma 8, the visit construction of
[NL] §1, Greendlinger's lemma for `Gr'_*(1/8)`, and [2C] Corollary 3.  With Lemma 8 above in its place it applies
verbatim: visits have `3` to `8` edges, and a 13-edge exterior arc then puts three consecutive edges of two
consecutive visits, in distinct copies, into one copy `C_M`. ∎

*Proof of Theorem R.*  Let `alpha beta = 0` with `alpha != 0` and `n <= 2`.  §1 normalizes to `alpha in k[K]`,
`k` infinite, `d >= 1`, `v_0 != 0 != v_d`.  Lemma 1 and Step 1 give the splitting.  Corollary 7 gives the
assumption of Lemma 8, and Proposition 9 is a contradiction.  So `alpha = 0`. ∎

*Proof of the Corollary.*  The involution `*` (`g -> g^{-1}`) is a `k`-linear anti-automorphism.  It sends
`k[<a>]` to itself and preserves the dimension of a coefficient span.
- `x = sum_j b^j v_j`, rank `<= 2`.  Left: Theorem R.  Right: `x gamma = 0` gives
  `gamma^* (sum_j v_j^* b^{d-j}) = gamma^* x^* b^d = 0`, which [AB] Theorem A excludes.
- `x = sum_j u_j b^j`, rank `<= 2`.  Left: [AB] Theorem A.  Right: `x gamma = 0` gives
  `(gamma^* b^{-d}) (sum_j b^{d-j} u_j^*) = gamma^* x^* = 0`, and Theorem R gives `gamma^* b^{-d} = 0`. ∎

## 6. Checks and what is open

- *`d = 1`.*  Then `n = 2`, a bad line is any good untouched line with a point at an `I` or `O` position, and
  §4 is [AB] Lemma 7 for `d = 1`.  Theorem R reproves Corollary C of [AB] for `b^{+1}`.
- *Calibration.*  In `H_{m,n} = <a, b | (a^m b)^n>`, `n >= 3`, the element `alpha = sum_{j<n} (b a^m)^j` gives
  `alpha (1 - b a^m) = 1 - (b a^m)^n = 0`, with `v_0 = 1`, `v_1 = -t^m`, so `n = 2`.  §2–§3 go through.  Every line of
  the relator loop carries the positions `{0, m}` and there are no distinct rows, so Lemma 5 fails and the
  determinant step says nothing.  Rows are the only input that separates `K` from `H_{m,n}` here.
- *Where the rank enters.*  Only Corollary 7.  For `n >= 3` a copy may have up to `n - 1` bad lines.  Lemma 6 is
  sharp as stated: the syzygy module has rank `n - 1`, and `n - 1` pure cosets in distinct rows are not excluded
  by the determinant.
- *Open: `n = 3`.*  At most two bad lines per copy.
  - A window `v_3, ..., v_8` avoiding `T_B` still has four middle lines, which is impossible.
  - A window containing `T_B` can hold `T_B`, two bad lines and three middle lines in alternate places.
    Windows `v_3, ..., v_{10}` cannot (five pairwise non-consecutive of eight), so visits in a copy with an
    untouched line at `T_B` have at most 10 edges, and all other visits at most 8.
  - The 13-edge count of [AB] Proposition 9 then fails only when the arc starts with at most 2 edges of a visit
    and continues with a visit of 9 or 10 edges through `T_B`.  Closing this needs one more edge in the
    Greendlinger arc, or a finer count at `T_B`.
- *Open: `n >= 4`* and mixed-layer supports.
