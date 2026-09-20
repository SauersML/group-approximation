# Two-output control forces rank loss at most the surplus (d = 1)

Agent: swarm-0917-w19-w19-gs-break, 2026-09-19. Target:
`local-rectangular-small-fibre-maps-lose-proportional-rank` (LRSF), test case
`K = 2`, `d = 1`.

## 0. Summary

**Theorem T.** Let `I, J` be finite, `eta > 0`, and let `g: T^I -> T^J` be continuous
(`T = R/Z`, sup metric). Suppose every input `i` has a set `C_i ⊆ J` with `|C_i| <= 2`
such that

> (C) `|g(u)_j - g(u')_j| < eta` for all `j in C_i` implies `||u_i - u'_i|| < 1/16`.

Then `rank g^* >= 2|I| - |J| = |I| - (|J| - |I|)` on `H^1(T^J; Z) -> H^1(T^I; Z)`.

- No locality hypothesis (L) is used: outputs may depend on all inputs.
- The constant is `C = 1`, and it is sharp: Proposition S at `k = 1` (small circles
  `T -> T^2`) gives equality `0 = 2m - 2m`.
- The bound is false for `|C_i| <= 3`: Proposition S at `k = 2` (tori of revolution
  `T^2 -> R^3 -> T^3`, where each angle is read from at most 3 coordinates) has
  `rank = 0 < 2(2m) - 3m`.

So the linear form of LRSF holds at `K = 2`, `d = 1` with `C(2, 1, eta) = 1`, even
without (L). Section 6 records what the proof gives for general `K` and where it
stops.

**Consequence for the graph's bookkeeping.** The node's remark "locality is
necessary" rests on [LEF] Theorem 3. That example (an injection `T^(N-1) -> T^N` into
a small ball) needs control sets of size `N`, not bounded size. So it shows only
that (C) with *unbounded* `|C_i|` is not enough. Whether (L) is needed once
`|C_i| <= K` is open for `K >= 3`, and Theorem T shows it is not needed at `K = 2`.

## 1. Notation

- `M` is the integer `J x I` degree matrix: `g^* x_j = row_j = sum_k M_(jk) pi_k`, where
  `x_j` and `pi_k` are the coordinate classes of `H^1(T^J)` and `H^1(T^I)`. So
  `rank g^* = rank_Q M`.
- `Z_0 ⊆ J` is the set of **zero rows**: outputs `j` with `row_j = 0`, i.e. with
  `g_j: T^I -> T` null-homotopic.
- `||t||` is the distance to `Z`. For `||p - q|| < 1/2`, `delta(p, q)` is the unique
  real number of absolute value `< 1/2` projecting to `q - p`.
- `H^*` is singular cohomology with `Z` coefficients.

## 2. Lemma N (coarse inverses are continuous on a neighbourhood)

**Lemma N.** Let `g` and `C_i` satisfy (C), and write `g_(C_i) = p_(C_i) o g: T^I -> T^(C_i)`,
with `Y_i = g_(C_i)(T^I)`. Then there are an open set `U_i ⊆ T^(C_i)` containing `Y_i`
and a continuous `psi_i: U_i -> T` such that `psi_i o g_(C_i)` is homotopic to the
coordinate map `pi_i: T^I -> T`. Hence `pi_i = g_(C_i)^* psi_i^* theta` in `H^1(T^I)`,
where `theta` generates `H^1(T)`.

*Proof.*
1. `Y_i` is compact. Cover it by finitely many open sup-balls `B_alpha` of radius
   `eta/2` centred at points `y_alpha in Y_i`. Put `U_i = ∪ B_alpha`. Pick
   `u^alpha in g_(C_i)^-1(y_alpha)` and set `p_alpha = u^alpha_i`.
2. For `y in U_i` let `S(y) = {alpha : y in B_alpha}`. If `alpha, beta in S(y)` then
   `y_alpha` and `y_beta` are `eta`-close in every coordinate of `C_i`. By (C) applied
   to `u^alpha, u^beta`, `||p_alpha - p_beta|| < 1/16`.
3. Take a partition of unity `(lambda_alpha)` on `U_i` with `supp lambda_alpha ⊆ B_alpha`.
   For `y in U_i` and any `alpha_0 in S(y)` put
   `psi_i(y) = p_(alpha_0) + sum_alpha lambda_alpha(y) delta(p_(alpha_0), p_alpha)`.
   - Every `alpha` with `lambda_alpha(y) > 0` lies in `S(y)`, so each displacement is
     defined and has absolute value `< 1/16`.
   - The value does not depend on `alpha_0`. For `alpha_0, alpha_1 in S(y)`,
     `delta(p_(alpha_0), p_alpha) = delta(p_(alpha_0), p_(alpha_1)) + delta(p_(alpha_1), p_alpha)`,
     because the terms have absolute values `< 1/16` and displacements add below `1/2`.
     Also `sum lambda_alpha = 1`.
   - `psi_i` is continuous. Near `y`, keep one `alpha_0 in S(y)`; it stays in `S(y')`
     for `y'` close to `y`, and the formula is then continuous in `y'`.
4. Let `u in T^I` and `y = g_(C_i)(u)`. For `alpha in S(y)`, `y` and `y_alpha` are
   `eta/2`-close on `C_i`, so (C) applied to `u, u^alpha` gives `||u_i - p_alpha|| < 1/16`.
   Re-basing the formula at `u_i` (step 3, second bullet) gives
   `psi_i(y) = u_i + epsilon(u)` with `epsilon(u) = sum lambda_alpha(y) delta(u_i, p_alpha)`,
   so `|epsilon(u)| < 1/16`. Also `epsilon(u) = delta(u_i, psi_i(g_(C_i)(u)))` is
   continuous in `u`.
5. `H(u, s) = u_i + s epsilon(u)` is a homotopy from `pi_i` to `psi_i o g_(C_i)`. ∎

## 3. Lemma D (the dichotomy)

**Lemma D.** Assume (C) with `|C_i| <= 2`. Then for every input `i` one of the
following holds:
- **(A)** `pi_i` lies in the `Q`-span of `{row_j : j in C_i}`;
- **(B)** `|C_i| = 2`, both rows of `C_i` are zero rows (`C_i ⊆ Z_0`), and `U_i != T^2`.

*Proof.* Let `m = |C_i|` and take `U_i, psi_i` from Lemma N.
1. *`U_i = T^(C_i)`.* Then `psi_i^* theta in H^1(T^m)` is an integer combination of
   the coordinate classes, so `pi_i = g_(C_i)^* psi_i^* theta` is an integer combination
   of the `row_j`, `j in C_i`. This is (A).
2. *`U_i` is a proper open subset of `T^m`.* Every component of `U_i` is a connected
   noncompact `m`-manifold, since a compact component would be clopen in `T^m`. So
   `H^m(U_i) = 0`: `H_m` vanishes and `H_(m-1)` is torsion-free (Hatcher, Prop. 3.29),
   and then universal coefficients apply.
   - `m = 0` is impossible: `pi_i` would factor through a point.
   - If `m = 1`, then `H^1(U_i) = 0` gives `pi_i = 0`, which is also impossible.
   - So `m = 2`, `C_i = {j, j'}`. For `j in C_i` the class `psi_i^* theta ∪ x_j|_(U_i)`
     lies in `H^2(U_i) = 0`. Pull it back by `g_(C_i): T^I -> U_i`. Since
     `g_(C_i)^* (x_j|_(U_i)) = g^* x_j = row_j`, this gives
     `0 = pi_i ∪ row_j = sum_(k != i) M_(jk) pi_i ∪ pi_k` in `H^2(T^I) = Λ^2 Z^I`.
     Hence `M_(jk) = 0` for every `k != i`, i.e. `row_j = M_(ji) pi_i`.
   - If `M_(ji) != 0` for some `j in C_i`, then `pi_i in Q row_j`, which is (A).
     Otherwise both rows vanish, which is (B). ∎

Let `A` be the set of inputs satisfying (A) and `B = I \ A`. Then
`span_Q{pi_i : i in A} ⊆ row space of M`, so

    rank M >= |A| = |I| - |B|.                                           (1)

## 4. Lemma L (a real function whose level strips kill two classes kills their product)

**Lemma L.** Let `X` be compact and `phi: X -> R` continuous, and let `a, b in H^1(X)`.
Suppose every `c in R` has an `epsilon > 0` such that `a` and `b` both restrict to `0`
on `phi^-1((c - epsilon, c + epsilon))`. Then `a ∪ b = 0`.

*Proof.*
1. The given intervals cover the compact image `[m, M'] = phi(X)`. Let `lambda > 0` be
   a Lebesgue number and take points `m = t_0 < t_1 < ... < t_r = M'` with spacing
   `Delta <= lambda/2`.
2. Put `I_k = (t_k - s, t_k + s)` with `Delta/2 < s < Delta`. Consecutive intervals
   overlap, `I_k ∩ I_l = ∅` for `|k - l| >= 2`, and each `I_k` has length `< lambda`,
   so it lies inside one of the given intervals. Together they cover `[m, M']`.
3. Let `P = phi^-1(∪_(k even) I_k)` and `Q = phi^-1(∪_(k odd) I_k)`. Both are open and
   `P ∪ Q = X`.
   - `P` is a disjoint union of the open sets `phi^-1(I_k)`, `k` even. `a` vanishes on
     each of them, and `H^1` of a disjoint union is the product, so `a|_P = 0`.
   - Likewise `b|_Q = 0`.
4. So `a` lifts to `H^1(X, P)` and `b` to `H^1(X, Q)`. The relative cup product
   `H^1(X, P) x H^1(X, Q) -> H^2(X, P ∪ Q) = H^2(X, X) = 0` is defined for open `P, Q`
   and is compatible with the absolute one (Hatcher, Section 3.2). Hence `a ∪ b = 0`. ∎

## 5. Lemma E (B-inputs have disjoint control sets)

**Lemma E.** If `i != i'` both lie in `B`, then `C_i ∩ C_(i') = ∅`.

*Proof.* Suppose `j in C_i ∩ C_(i')`. Write `C_i = {j, j_2}` and `C_(i') = {j, j_3}`,
with `j_2 = j_3` allowed. By (B), `j, j_2, j_3 in Z_0`.
1. *A 2-torus.* Let `tau: T^2 -> T^I` put `(t, s)` at sites `i, i'` and `0` elsewhere,
   and let `h = g o tau`. Then `tau^* pi_i = theta_1` and `tau^* pi_(i') = theta_2` are
   the coordinate classes, and `theta_1 ∪ theta_2` generates `H^2(T^2)`.
2. *Lifting the zero rows.* Since `g^* x_l = 0` for `l in {j, j_2, j_3}`, each `h_l` is
   null-homotopic. So `h_l = phi_l mod 1` for continuous `phi_l: T^2 -> R`. Put
   `phi = phi_j`.
3. *The classes on the plane.* Let `rho: R^2 -> T^2` be the covering in the coordinates
   `(x_j, x_(j_2))`. Let `U~ = rho^-1(U_i)` and `Psi = psi_i o rho: U~ -> T`. The map
   `Phi = (phi, phi_(j_2)): T^2 -> U~` satisfies `rho o Phi = h_(C_i)`. By Lemma N,
   `theta_1 = tau^* pi_i = Phi^* Psi^* theta`.
4. *Strips.* Fix `c in R`. Let `K = Phi(T^2)`, which is compact, `L = {y : (c, y) in K}`
   and `O = {y : (c, y) in U~}`, which is open and contains `L`.
   - Cover the compact set `L` by finitely many open intervals `J_1, ..., J_n` with
     pairwise disjoint closures, each closure contained in `O`. Use the components of
     `O`, which are open intervals, and shrink each one to a neighbourhood of its
     compact part of `L`.
   - By the tube lemma there is an `epsilon > 0` with
     `[c - epsilon, c + epsilon] x cl(J_k) ⊆ U~` for all `k`.
   - Shrinking `epsilon`, `K ∩ ([c - epsilon, c + epsilon] x R) ⊆ R x ∪ J_k`. Otherwise
     points of `K` with first coordinate tending to `c` and second coordinate outside the
     open set `∪ J_k` would have a limit in `K ∩ ({c} x R)`, outside `∪ J_k`. That
     contradicts `L ⊆ ∪ J_k`.
   - Hence `Phi` maps `phi^-1((c - epsilon, c + epsilon))` into the disjoint union of the
     open rectangles `(c - epsilon, c + epsilon) x J_k ⊆ U~`. Each rectangle is
     contractible, so `Psi^* theta` vanishes on their union, and therefore `theta_1`
     vanishes on `phi^-1((c - epsilon, c + epsilon))`.
5. *The same for `i'`.* The same argument with `(phi, phi_(j_3))` and `U_(i')` shows that
   `theta_2` vanishes on the strips `phi^-1((c - epsilon', c + epsilon'))`. Use
   `min(epsilon, epsilon')`.
6. Lemma L with `X = T^2` gives `theta_1 ∪ theta_2 = 0`, contradicting step 1. ∎

The shared zero row `x_j` is the function whose level strips separate the two classes.
This is the cohomological form of the elementary fact that a real function on a
product cannot have both two rows and two columns with disjoint ranges.

## 6. Proof of Theorem T

By Lemma D, every `i in B` has `C_i ⊆ Z_0` with `|C_i| = 2`. By Lemma E these sets are
pairwise disjoint, so `|Z_0| >= 2|B|`. The nonzero rows number at least `rank M`, so

    |J| >= |Z_0| + rank M >= 2|B| + rank M.                               (2)

Combine (1) and (2): `|J| >= 2(|I| - rank M) + rank M`, i.e.
`rank g^* = rank M >= 2|I| - |J|`. ∎

**Sanity checks.**
- *Square case, `|J| = |I|`.* Full rank follows. This reproves [LEF] Theorem 1 when
  `d = 1` and `|C_i| <= 2`, by a different route that uses no top homology of `T^N`.
- *Proposition S, `k = 1`.* `m` small circles `T -> T^2` give `B = I` and `Z_0 = J`.
  Lemma E holds with equality and `rank = 0 = 2m - 2m`.
- *Proposition S, `k = 2`.* This has `|C_i| = 3`. Lemma D fails there, because a
  proper open `U ⊆ T^3` can have `H^2(U) != 0`.

## 7. General `K`: what survives, and the prerequisite that would finish the job

**Lemma D_K.** Let `d = 1` and `|C_i| = m`, with `m` arbitrary. Let `R_i` be the
`Q`-span of `{row_j : j in C_i}`. Then either `pi_i in R_i`, or `dim R_i <= m - 2`.

*Proof.*
1. If `U_i = T^m`, argue as in Lemma D, step 1.
2. Otherwise `H^m(U_i) = 0`. So `psi_i^* theta ∪ x_(j_1) ∪ ... ∪ x_(j_(m-1)) = 0` for
   distinct `j_1, ..., j_(m-1)` in `C_i`, and pulling back gives
   `pi_i ∧ row_(j_1) ∧ ... ∧ row_(j_(m-1)) = 0` in `Λ^m Q^I`.
3. If `dim R_i >= m - 1`, choose `m - 1` independent rows. Their wedge is a nonzero
   decomposable `omega`, and `pi_i ∧ omega = 0` forces `pi_i` into their span. ∎

So an input outside the row span of its own control rows sees a rank drop of at least
2 among them. Let `B` be the set of such inputs, `P = ∪_(i in B) C_i`, and
`defect(P) = |P| - dim span{row_j : j in P}`.

**Reduction R.** Suppose that for some `c_K < 1`:

> **(E_K)** `|B| <= c_K defect(P)` for every map satisfying (C) with `|C_i| <= K`.

Then the linear form of LRSF holds at `d = 1` with `C = c_K / (1 - c_K)`, with or without
(L).

*Proof.*
1. The rows outside `P` have rank at least `rank M - dim span(rows of P)`, so
   `|J| >= defect(P) + rank M`.
2. With `L = |I| - rank M` and `|I \ B| <= rank M` (Lemma D_K), `|B| >= L`.
3. So `|J| - |I| = (|J| - rank M) - L >= |B| / c_K - L >= L (1/c_K - 1)`. ∎

**Status of (E_K).**
- `c_2 = 1/2` is Lemma E. It is sharp at Proposition S, `k = 1`.
- Proposition S at `k = K - 1` has `|B| = K - 1` and `defect(P) = K`. So `c_K >= (K-1)/K`,
  which matches `C = K - 1`.
- For `K >= 3`, (E_K) is **open**. The proof of Lemma E does not transfer. A shared
  zero row `x_j` gives only one real function. Its level strips kill the classes of
  inputs whose remaining control coordinates form a 1-dimensional slice, and that
  happens only when `|C_i| <= 2`. For `|C_i| = 3` the slices of `U_i` are open subsets
  of `T^2` or `R^2` and carry `H^1`. This is exactly the torus-of-revolution mechanism.
- A proof for `K = 3` would have to replace Lemma L by a two-function version: level
  sets of `(x_j, x_(j'))` for two shared zero rows, or a Lusternik–Schnirelmann count of
  the cylinders `p_(C_i)^-1(U_i)`.
