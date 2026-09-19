---
rg: 2
id: gaussian-pair-sum-chaos-eigenvalue-pattern-count-proof
kind: route
title: Expand Pi^(tensor D) over the subsets the involution acts on, replace each matching-average kernel by the uniform average over its equality-pattern cell, and count the pattern cells that survive centring
target: gaussian-pair-sum-chaos-eigenvalues-halve-every-two-degrees
requires: []
artifacts:
  - experiments/gaussian-rich-2to1-universe-2026-09-17/check_gaussian_universe.py
---

Notation is as in the target. Tuples `i in [m]^D` index the standard basis of
`(R^m)^(tensor D)`. `v in V_D` means that `v` sums to 0 along each coordinate:
`sum_(x in [m]) v(i with i_t := x) = 0` for every `t` and every choice of the
other coordinates. Write `(m)_q = m(m-1)...(m-q+1)`.

**Step 1 (monotone).** For `k >= j`, the tensor factors commute and are
projections, so `Pi^(tensor k) = Pi^(tensor j) tensor Pi^(tensor (k-j)) <= Pi^(tensor j) tensor I`
in the PSD order. Averaging over `sigma` gives `M_k <= M_j tensor I` on
`V_k = V_j tensor V_(k-j)`. The right side has norm `lambda_j` there.

**Step 2 (degree one).** `E sigma = (J - I)/(m-1)`, since the partner of `a`
is uniform on `[m] \ {a}`. On `1^perp` this is `-1/(m-1)`. So
`M_1 = (1 - 1/(m-1))/2 = (n-1)/(2n-1)`.

**Step 3 (subset expansion).** `Pi^(tensor D) = 2^-D sum_(S subset [D]) sigma^(S)`,
where `sigma^(S)` applies `sigma` in the coordinates in `S` and the identity
elsewhere. Put `K_S = E_sigma sigma^(S)`. This is a Markov kernel on `[m]^D`.
It is symmetric: `sigma^(S)` is an involution, so `sigma^(S) i = j` iff
`sigma^(S) j = i`. Hence `M_D = 2^-D sum_S K_S`.

**Step 4 (cells).** Fix `S`. The *cell* of `i` is the set `C` of tuples `j`
with `j_(S^c) = i_(S^c)` whose restriction `j_S` has the same equality pattern
`pi in Part(S)` as `i_S`. Values may coincide with values of `i_(S^c)`. If
`pi` has `q` blocks, then `|C| = (m)_q`. The cells partition `[m]^D`. Let
`Q_S` be the kernel that averages uniformly over cells:
`Q_S(i, j) = 1/|C|` for `j in C(i)`. It is symmetric, and

`<v, Q_S v> = sum_C (sum_(j in C) v(j))^2 / |C|`.

**Step 5 (`K_S` is close to `Q_S`).** Row `i` of `K_S` gives `j_S` the
pattern `pi`, with block values `(sigma(u_1), ..., sigma(u_q))`. Here
`u_1, ..., u_q` are the distinct values of `i_S`, `U = {u_r}` and `q <= |S| <= D`.
Row `i` of `Q_S` gives the same pattern with a uniform injective value tuple.

* Let `E` be the event that no two `u_r` are matched to each other. Then
  `Pr[not E] <= binom(q,2)/(m-1)`.
* On `E`, the value tuple is injective with values in `W = [m] \ U`. Its
  conditional law is invariant under every permutation of `W` fixing `U`
  pointwise. Such permutations preserve the matching law and `E`, and
  `tau sigma tau^-1 (u_r) = tau(sigma(u_r))`. `Sym(W)` is transitive on
  injective `q`-tuples of `W`, so on `E` the tuple is uniform on them.
* A uniform injective `q`-tuple of `[m]` meets `U` with probability at most
  `q^2/(m-q+1)`.

So the two rows are at total variation at most `2 q^2/(m-q) <= 2D^2/(m-D)`.
Hence `K_S - Q_S` is symmetric with every absolute row sum at most
`4D^2/(m-D)`. By the Schur test, `||K_S - Q_S|| <= 4D^2/(m-D)`. Averaging:

`||M_D - 2^-D sum_S Q_S|| <= 4D^2/(2n-D)`. (5)

Fix a unit `v in V_D`. We bound `2^-D sum_S <v, Q_S v>` by splitting the cells
of each `S` according to their pattern `pi`.

**Step 6 (patterns with a singleton are small).** Suppose `pi` has a singleton
block `{t}`, with `t in S`. Pick one such `t` for each `pi`. A tuple in `C`
consists of an injective assignment `beta` of values to the other `q - 1`
blocks, plus a value `x` at `t` outside `values(beta)`. Centring in coordinate
`t` gives

`sum_(x not in values(beta)) v(beta, x) = - sum_(w in values(beta)) v(beta, w)`.

So `sum_C v = - sum_((beta, w)) v(beta, w)`. The tuples `(beta, w)` are
distinct, and there are `N = (m)_(q-1) (q-1)` of them; call this set `R_C`.
By Cauchy--Schwarz, `(sum_C v)^2 / |C| <= (N/|C|) sum_(R_C) v^2`, and
`N/|C| = (q-1)/(m-q+1) <= D/(2n-D)`. For fixed `(S, pi, t)`, distinct values
of `i_(S^c)` give disjoint sets `R_C`. Summing over the cells of this `pi`
therefore gives at most `D/(2n-D)`. There are at most `Bell(|S|) <= Bell(D)`
patterns, so these cells contribute at most `Bell(D) D/(2n-D)` to each
`<v, Q_S v>`, and the same after averaging over `S`.

**Step 7 (patterns without a singleton).** Now every block of `pi` has size at
least 2. Let `u` be the number of distinct values of `i_(S^c)`, so `u <= D`.
Split `C` by the *merge map* `phi`. This is an injective partial map from the
blocks of `pi` to `values(i_(S^c))`, recording which blocks take a value
already used outside `S`. Let `r = |dom phi|`, let `C_phi` be its part of `C`,
and let `C_0` be the part with `r = 0`.

* There are at most `(u+1)^q <= (D+1)^D` merge maps.
* `|C_phi| = (m-u)_(q-r) <= m^(q-r)`.
* `|C| = (m)_q >= m^q (1 - D/m)^D`.

So `|C_phi|/|C| <= (1 - D/(2n))^-D / (2n)` when `r >= 1`.

Write `sum_C v = a_0 + b`, with `a_0 = sum_(C_0) v` and `b` the rest. Use
`(a_0 + b)^2 <= (1+eps) a_0^2 + (1 + 1/eps) b^2`.

* **The `b` part.** By Cauchy--Schwarz twice,
  `b^2 <= (D+1)^D sum_(phi != 0) |C_phi| sum_(C_phi) v^2`. So
  `b^2/|C| <= (D+1)^D (1-D/(2n))^-D (2n)^-1 sum_(C \ C_0) v^2`.
  The cells of a fixed `S` partition `[m]^D`, so summing over all cells of
  `S` gives at most `(D+1)^D (1-D/(2n))^-D/(2n)`.
* **The main part.** `|C_0| <= |C|`, so `a_0^2/|C| <= sum_(C_0) v^2` by
  Cauchy--Schwarz. Sum over `S`, over patterns `pi` without a singleton, and
  over cells. Let `kappa(i)` be the equality pattern of the whole tuple `i` on
  `[D]`. The tuple `i` lies in `C_0` of its `S`-cell exactly when the values of
  `i_S` avoid those of `i_(S^c)`, that is, when `S` is a union of blocks of
  `kappa(i)`. Its pattern then has no singleton exactly when all these blocks
  have size at least 2. So `i` is counted for exactly `2^(q_2(i))` sets `S`,
  where `q_2(i)` is the number of blocks of `kappa(i)` of size at least 2.
  Since `q_2(i) <= floor(D/2)`,

  `2^-D sum_S sum_(C_0 cells) sum v^2 <= 2^(floor(D/2) - D) ||v||^2 = 2^-ceil(D/2)`.

**Step 8 (assembly).** Combine (5) with Steps 6 and 7. The `b` part is summed
with the weight `2^-D` over the `2^D` sets `S`:

`<v, M_D v> <= (1+eps) 2^-ceil(D/2) + (1+1/eps)(D+1)^D (1-D/(2n))^-D/(2n) + Bell(D) D/(2n-D) + 4D^2/(2n-D)`.

`M_D` is PSD and preserves `V_D`, so `lambda_D` is the supremum of the left
side over unit `v in V_D`. This is item 3. With `eps = n^(-1/2)`, every error
term is `O_D(n^(-1/2))`.

**Consistency with exact values.** The artifact checks item 2 to `1e-9` for
`n = 2..5`. The exact `lambda_3` at `n = 4` and `n = 5` is `0.2466` and
`0.2468`, just below the limit `1/4`. At small `n` the main term is not an
upper bound: for `n = 2`, `lambda_3 = 1/3`. The theorem is asymptotic in `n`
at each fixed `D`, and that is all that is used downstream.
