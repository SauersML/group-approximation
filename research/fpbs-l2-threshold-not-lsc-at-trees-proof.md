---
rg: 2
id: fpbs-l2-threshold-not-lsc-at-trees-proof
kind: route
title: Coset-tree edge count, Folner lower bound on the connectivity operator of the amenable factor, finite-by-Z^m approximants of F_m, Easo--Hutchcroft locality, and a Busemann Schur test on the tree
target: fpbs-l2-threshold-not-lsc-at-trees
requires:
  - fpbs-easo-hutchcroft-pc-locality
  - fpbs-mohar-adjacency-norm-cheeger-bound
  - fpbs-direct-limit-certificates-add-no-slack
artifacts:
  - experiments/fpbs-involution-free-product-l2-drop-2026-09-17/check.py
---

Notation is that of the claim.

**Imported nodes.**
- [EH] `fpbs-easo-hutchcroft-pc-locality`: locality of `p_c` for infinite
  transitive graphs with `p_c != 1`.
- [Mo] `fpbs-mohar-adjacency-norm-cheeger-bound`: `||A_G|| <= sqrt(d^2 - h^2)`
  for `d`-regular `G` with edge expansion `h`.
- [Cov] Lemma 2.1 of `research/artifacts/fpbs-direct-limit-certificates-2026-09-17.md`,
  part of `fpbs-direct-limit-certificates-add-no-slack`: a covering map
  `X -> Y` of connected locally finite graphs gives `p_c(X) <= p_c(Y)`.

**Textbook facts used.**
- (T1) `p_c(T_d) = 1/(d-1)`. The cluster is a Galton--Watson tree.
- (T2) Harris--FKG.
- (T3) Følner sets exist in every finitely generated amenable group.
- (T4) The normal form theorem for free products.
- (T5) `p_c(Z^2) < 1` (Peierls contours), and
  `rho(T_d) = 2 sqrt(d-1)/d` (Kesten).
- (T6) Schur test: for a symmetric kernel `K >= 0` and a function `h > 0`,
  `||K|| <= sup_u sum_v K(u,v) h(v)/h(u)`.

The script `check.py` checks the counts in Steps 1 and 6 by brute force, the
identity in Remark 9, and the numbers. It is a sanity check, not part of the
proof.

## Step 1. Edge expansion of `A * Z/2`

1. **Setup.** Let `G = Cay(A * <c>, S_A ∪ {c})`, where `A` is infinite with
   `|S_A| = D`.
   * Each vertex `g` lies in one left coset `gA`.
   * The coset `gA` spans a copy of `Cay(A, S_A)`, which is infinite and
     connected.
   * Each vertex has exactly one `c`-edge `{g, gc}`.
2. **Two facts from (T4).**
   * `gc` is not in `gA`, since `c` is not in `A`.
   * Two cosets are joined by at most one `c`-edge. Suppose `x != y` in `gA`
     have `xc` and `yc` in a common coset. Then `y = x a` with `a` in
     `A \ {e}`, and `(xc)^{-1} yc = c a c` would lie in `A`. But `c a c` is a
     reduced normal form of length 3.
3. **The coset graph is a tree.** Its vertices are the `A`-cosets and its
   edges are the `c`-edges.
   * A cycle `C_1, ..., C_r, C_1` with `r >= 3` and distinct consecutive
     `c`-edges gives a closed path in `G`. The path crosses a `c`-edge into
     `C_i` at `y_i`, moves inside `C_i` by `a_i in A`, and leaves through the
     `c`-edge at `x_i = y_i a_i`.
   * Since each vertex has one `c`-edge and the consecutive edges are
     distinct, `a_i != e` for every `i`.
   * So `a_1 c a_2 c ... a_r c = e` with all `a_i != e`. This contradicts
     (T4).
   * Cycles of length `r <= 2` are excluded by item 2.
4. **Counting.** Let `F` be finite and nonempty, and let `m` be the number of
   cosets it meets.
   * The `c`-edges with both ends in `F` form a subforest of the coset tree on
     those `m` cosets, so there are at most `m - 1` of them.
   * So at least `|F| - 2(m-1)` `c`-edges leave `F`.
   * Each nonempty `F ∩ C` is a finite subset of the infinite connected graph
     on `C`, so at least one `S_A`-edge of `C` leaves it.
   * Hence `|∂_E F| >= m + |F| - 2m + 2 = |F| - m + 2`, and also
     `|∂_E F| >= m`.
   * If `m <= |F|/2` the first bound gives `|∂_E F| > |F|/2`. Otherwise the
     second does.
5. **Spectral radius.** By [Mo] with `h >= 1/2` and `d = D + 1`,
   `rho = ||A_G||/d <= sqrt(1 - 1/(4d^2)) <= 1 - 1/(8d^2)`.

This proves (A)1.

## Step 2. `p_(2->2)(A * Z/2) <= p_c(A)`

1. **Subgraph comparison.** Let `p > p_c(A)`. The identity coset `A` spans
   `Cay(A, S_A)` as a subgraph of `G`. So `tau^G_p(u,v) >= tau^A_p(u,v)` for
   `u, v in A`, by the monotone coupling.
2. **Infinite susceptibility.** With positive probability `|K^A_o| = infinity`,
   so `chi_A(p) = sum_x tau^A_p(o,x) = infinity`.
3. **Følner bound.** Fix `R` and let `B_R` be the `R`-ball of `Cay(A)`. By
   (T3) there are finite `F_j` in `A` such that the fraction of `u in F_j`
   with `u B_R` inside `F_j` tends to `1`. Left invariance gives
   `tau(u, ux) = tau(o, x)`. So for `f = 1_(F_j)`:

   ```text
   <f, T^G_p f> / ||f||^2  >=  |F_j|^{-1} sum_{u in F_j, u B_R ⊆ F_j} sum_{x in B_R} tau^A(o,x)
                           ->  sum_{x in B_R} tau^A_p(o,x).
   ```

4. **Conclusion.** Let `R -> infinity`. Then `||T^G_p|| >= chi_A(p) = infinity`
   for every `p > p_c(A)`, so `p_(2->2)(G) <= p_c(A)`.

This proves (A)2. Amenability of `A` is used only in item 3.

## Step 3. Amenable approximants of `F_m`

1. **Finite quotients with large girth.** Let `w = y_1 ... y_L` be a
   nontrivial reduced word in `x_1^{±1}, ..., x_m^{±1}`. Build partial
   injections on `{0, ..., L}`: if `y_t = x_i^{ε}`, set `sigma_i^{ε}(t-1) = t`.
   * A point `t` is touched only by `y_t` and `y_(t+1)`.
   * A conflict at `t` would need `y_(t+1) = y_t^{-1}`, which reducedness
     excludes.
   * Extend each `sigma_i` to a permutation of `{0, ..., L}`. Then `w` moves
     `0` to `L != 0`, so `w` acts nontrivially.
   * Let `Q_R` be the image of `F_m` in the product of these finite
     permutation groups, over all nontrivial reduced `w` with `|w| <= R`. No
     such `w` is trivial in `Q_R`.
2. **The groups `A_R`.** Let `A_R` be the subgroup of `Q_R x Z^m` generated by
   `alpha_i = (x_i, e_i)`, and let `phi : F_m -> A_R` send `x_i` to `alpha_i`.
   * `phi(w) = (w mod Q_R, abelianisation of w)`.
   * So `phi(w) != e` for every nontrivial reduced `w` with `|w| <= R`. In
     particular the `2m` elements `alpha_i^{±1}` are distinct and nontrivial.
   * Hence `(A_R; alpha)` agrees with `(F_m; x)` on all relations of length at
     most `R`, and `A_R -> F_m` in the space of `m`-marked groups.
3. **Amenable and infinite.** The projection `A_R -> Z^m`, `alpha_i -> e_i`,
   is onto, with kernel inside the finite group `Q_R x {0}`. So `A_R` is
   finite-by-abelian, hence amenable and infinite.
4. **`p_c(A_R) < 1`.** The projection is label preserving, so it induces a
   covering map `Cay(A_R) -> Cay(Z^m, {±e_i})`. By [Cov],
   `p_c(A_R) <= p_c(Z^m) <= p_c(Z^2) < 1`. The middle inequality holds because
   `Z^2` is a subgraph, and the last is (T5).

## Step 4. Convergence of the free products

Let `G_R = (A_R * Z/2; alpha_1, ..., alpha_m, c)`.

1. **Words map to normal forms.** Let `w` be a word in `x_i^{±1}` and `c` of
   length at most `R`, nontrivial in `F_m * Z/2`. Write it in normal form
   `u_0 c u_1 c ... c u_s`. Here each `u_j` is a reduced word in `F_m` of
   length at most `R`, and `u_j != e` for `0 < j < s`.
2. **The image stays reduced.** By Step 3.2, each nontrivial `u_j` maps to a
   nontrivial element of `A_R`. So the image is a reduced normal form in
   `A_R * Z/2`.
3. **It is nontrivial.** By (T4) the image is nontrivial unless `s = 0` and
   `u_0 = e`. That case is excluded because `w != e`.
4. **Conclusion.** `G_R -> (F_m * Z/2; x, c)` as `k`-marked groups, with
   `k = m + 1`.
5. **The limit is a tree.** Reduced normal forms of `F_m * Z/2` correspond to
   nonbacktracking paths in its Cayley graph on `{x_i^{±1}, c}`. So that
   Cayley graph is the `(2m+1)`-regular tree `T_(2k-1)`.
6. **Membership.** All `G_R` and the limit are simple, `(2k-1)`-regular, and
   satisfy `c^2 = e`. By Step 1 their spectral radius is at most `1 - eta_k`,
   with `eta_k = 1/(8(2k-1)^2)`. The tree is Step 1 with `A = F_m`. So all of
   them lie in `Z_(k,eta_k,s_k^2)`.

## Step 5. Thresholds by locality

1. **The factors.** `A_R -> F_m` and `p_c(A_R) != 1` by Step 3.4. Also
   `Cay(F_m) = T_(2m)`. So [EH] and (T1) give
   `p_c(A_R) -> 1/(2m-1) = 1/(2k-3)`.
2. **The free products.** `Cay(A_R)` is a subgraph of `Cay(G_R)`, so
   `p_c(G_R) <= p_c(A_R) < 1`. With Step 4, [EH] and (T1) give
   `p_c(G_R) -> 1/(2k-2)`.
3. **The upper bound.** By Step 2,
   `limsup p_(2->2)(G_R) <= lim p_c(A_R) = 1/(2k-3)`.

## Step 6. `p_(2->2)(T_d) >= 1/sqrt(d-1)`

1. **Setup.** On `T_d`, `tau_p(u,v) = p^{d(u,v)}`. Fix an end `xi` with
   Busemann function `beta`, and put `h = (d-1)^{-beta/2}`.
2. **Counting.** A vertex `v` at distance `n` from `u` is reached by going
   `j` steps toward `xi` and then `n - j` steps away.
   * Then `beta(v) - beta(u) = n - 2j`.
   * There are at most `(d-1)^{n-j}` such `v` for each `j`.
3. **The row sum.**

   ```text
   sum_{d(u,v)=n} h(v)/h(u) <= sum_{j=0}^{n} (d-1)^{n-j} (d-1)^{-(n-2j)/2} = (n+1)(d-1)^{n/2}.
   ```

4. **Schur test.** By (T6),
   `||T_p|| <= sum_n (n+1)(p sqrt(d-1))^n = (1 - p sqrt(d-1))^{-2}`, which is
   finite for `p < 1/sqrt(d-1)`.
5. **Conclusion.** For `d = 2k-1` this gives
   `p_(2->2)(T_(2k-1)) >= 1/sqrt(2k-2)`.
6. **Strictness.** `1/(2k-3) < 1/sqrt(2k-2)` iff `(2k-3)^2 > 2k-2`, which
   holds for `k >= 3`.

This proves (B).

## Step 7. Consequences

1. **No lower semicontinuity.** This is (B) itself.
2. **`T_5` is not an interior point.** Let `k = 3` and `delta in (1/12, 1/4)`.
   * `T_5` lies in `U_(M',delta)` with `M' = ||T_(1/4+delta)|| < infinity`,
     by Step 6.
   * By Step 5, `p_c(A_R) - p_c(G_R) -> 1/12 < delta`. So for large `R`,
     `p_c(G_R) + delta > p_c(A_R)`, and Step 2 gives
     `||T^(G_R)_(p_c(G_R)+delta)|| = infinity`.
   * The same computation for general `k` gives the cap
     `delta <= 1/(2k-3) - 1/(2k-2)` in the killed-class statement, and the cap
     `q <= 1/(2k-3)`.
3. **The jump of `rho`.**
   * Entrywise `tau_q <= sum_n q^n A_G^n`, summing over walks, and
     `||A_G^n|| = (d rho)^n`. So `p_(2->2)(G) >= 1/(d rho(G))`.
   * With Step 2, `rho(G_R) >= 1/(d p_c(A_R))`, which tends to
     `(2k-3)/(2k-1)`.
   * This exceeds `rho(T_(2k-1)) = 2 sqrt(2k-2)/(2k-1)` (T5) iff
     `(2k-3)^2 > 4(2k-2)`, that is iff `4k^2 - 20k + 17 > 0`, which holds for
     `k >= 4`.

## Step 8. Not a counterexample

`fpbs-free-product-cayley-graphs-have-critical-l2-gap` gives
`p_c(G_R) < p_(2->2)(G_R)`. This route uses only upper bounds on
`p_(2->2)(G_R)`, so it is consistent with that theorem.

## Remark 9. Consistency check

`p_c(T_5) = 1/4` is the root of `p (chi_(T_4)(p) - 1) = 1`, with
`chi_(T_4)(p) = (1+p)/(1-3p)`. This is the two-block criterion of the
free-product theorem, applied to the limit `F_2 * Z/2`. `check.py` verifies it.
