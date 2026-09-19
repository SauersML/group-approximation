---
rg: 2
id: gstar-star-linearity-is-stable-near-full-value-proof
kind: route
title: Charge every twisted star to unsat edges inside the Fano sub-configurations R/W0 (exact constant 4/3), run BLR on the star quotient F_2^n/W with random values off the satisfied set, and glue per-star references along Grassmann edges using the spectral gap theta_1/theta_0 < 1/2
target: gstar-star-linearity-is-stable-near-full-value
requires:
  - list-star-coherent-selector-witnesses-put-np-in-rp
artifacts:
  - experiments/ugc-gstar-stability-2026-09-17/fano_twist.py
  - experiments/ugc-gstar-stability-2026-09-17/check_stability.py
---

Notation is that of the target. All spaces are over `F_2`. For a subspace
`S`, a *label* on `S` is a linear functional on `S`.

* A `W` always has dimension `l-1`, a `T` dimension `l`, and an `R`
  dimension `l+1`.
* For `W < R`, the three `T` with `W < T < R` form the *star of `W` in `R`*.
* The star is *full* if its three edges `(W,T)` are satisfied. It is
  *twisted* if it is full and the three labels `F(T)` have no common
  extension to a functional on `R`.
* Put `t_W := Pr_{R > W}[star of W in R is twisted]` and `t := E_W t_W`.

## Step 0: val and eps

Write `m = n-l+1`. For fixed `W`:

* `Pr_u[u in W] = 2^-m`.
* Conditioned on `u notin W`, `T = W+u` is a uniform `T > W`.

So `val = (1 - 2^-m)(1 - eps)`. Hence `1 - val = 2^-m + (1-2^-m) eps >= eps`.

## Step 1: Lemma F7 (Fano charging)

Fix an `R` and a subspace `W0 < R` with `dim W0 = l-2`. The *Fano
configuration* `Fano(W0)` consists of:

* the 7 subspaces `W` with `W0 < W < R`;
* the 7 subspaces `T` with `W0 < T < R`;
* the 21 incident pairs `(W,T)`.

Choose a complement `E` of `W0` in `R`, so `dim E = 3`. Then:

* `W = W0 + x` for a unique point `x` of `PG(E)`, and
  `T = W0 + (T cap E)` for a unique line `T cap E` of `PG(E)`.
* A label on `T` is a pair `(alpha, beta)`, where `alpha = F(T)|_W0` is the
  *colour* and `beta = F(T)|_(T cap E)`, one of 4 values.
* A label on `W` is a pair (colour, bit at `x`).
* `(W,T)` is satisfied iff the colours agree and `beta_T(x)` equals the bit.
* The labels of a full star at `W` all have colour `F(W)|_W0`. They have a
  common extension to `R = W0 + E` iff the three `beta` of the lines through
  `x` have a common extension to `E`.

**Lemma F7.** In every `Fano(W0)`, `#twisted stars <= (4/3) #unsat edges`.
Here a star means the star of some `W` of `Fano(W0)` in `R`. Its three `T`
all contain `W0`, so they lie in `Fano(W0)`.

*Proof.* First fix the `T` labels and replace each `W` label by a plurality of
the three votes `(alpha_T, beta_T(x))` of the lines through `x`. This does not
increase the number of unsat edges. It does not change which stars are full:
a star is full iff its three votes agree, and then the original `W` label was
that common vote. So we may assume plurality `W` labels.

Only the partition of the 7 lines into colour classes matters. So the
labellings to check are the `877 = Bell(7)` set partitions times `4^7`
choices of `beta`. `fano_twist.py all` enumerates all of them and computes the
exact ratio.

* The maximum of #twisted / #unsat is `4/3`.
* It is attained, for example at 4 twisted stars against 3 unsat edges, with
  one colour.
* No labelling with 0 unsat edges has a twisted star.

`[]`

## Step 2: t <= 4 eps

Fix `R`. Put `N1 := 2^(l-1) - 1`, the number of `(l-2)`-subspaces of an
`(l-1)`-space.

* The star of `W` in `R` lies in `Fano(W0)` for exactly the `N1` choices
  `W0 < W`. Its twisted status is the same in every one of them.
* An edge `(W,T)` inside `R` lies in `Fano(W0)` for exactly the `N1` choices
  `W0 < W`.

Summing Lemma F7 over all `W0 < R` and dividing by `N1` gives
`tw_R <= (4/3) unsat_R`, the per-`R` counts.

Now sum over `R`. Let `N_R := [m choose 2]_2` be the number of `R > W`. Each
`T` lies in `2^(m-1) - 1` of the `R`, and each `W` lies in `2^m - 1` of the
`T`. Hence

* `sum_R tw_R = N_R sum_W t_W`;
* `sum_R unsat_R = (2^m - 1)(2^(m-1) - 1) sum_W eps_W = 3 N_R sum_W eps_W`.

So `t <= 4 eps`.

## Step 3: BLR on the star quotient

Fix `W` and an extension `psi0` of `F(W)` to `F_2^n`. Let `Q := F_2^n / W`,
so `dim Q = m`, and let `pi` be the quotient map. Let `S` be the set of
`x != 0` in `Q` for which the edge `(W, W + u)` is satisfied, where
`pi(u) = x`. The set `S` is well defined.

For `x` in `S`, put `f(x) := F(W+u)(u) - psi0(u)`. This is well defined: if
`u' = u + w` with `w` in `W`, then
`F(W+u)(w) = F(W)(w) = psi0(w)`.

Extend `f` to all of `Q` by `f(0) = 0` and independent uniform bits on
`Q \ (S + 0)`.

Every extension `psi` of `F(W)` equals `psi0 + l o pi` for a unique linear
`l` on `Q`. For satisfied `u`, `F(W+u)(u) != psi(u)` iff `f(x) != l(x)`.
Hence, for every realisation of the random bits,

    min_psi D_W(psi) <= min_l Pr_{x in Q}[f(x) != l(x)] =: dist(f).

**BLR bound.** For `g : F_2^m -> F_2` with `g(0) = 0`, let
`rej(g) := Pr_{x,y}[g(x) + g(y) + g(x+y) = 1]`, with `x, y` independent and
uniform. Then `rej(g) >= dist(g)`.

*Proof.* Put `G = (-1)^g`. Then `1 - 2 rej = sum_a Ghat(a)^3`, which is at
most `max_a Ghat(a) * sum_a Ghat(a)^2 = max_a Ghat(a) = 1 - 2 dist(g)`. `[]`

Now bound `E rej(f)` over the random bits. A pair `(x,y)` with `x = 0`,
`y = 0` or `x = y` never rejects, because `f(0) = 0`. Otherwise
`{0, x, y, x+y}` is a 2-plane `Pi` of `Q`, and `W + Pi = R` is an `R > W`.
Given that the pair is non-degenerate, `R` is uniform.

* If all three nonzero points of `Pi` are in `S`, the star of `W` in `R` is
  full. Then the test rejects iff the star is twisted. To see this, put
  `h := F(T) - psi0|_T` on each of the three `T`. Each `h` vanishes on `W` and
  is a functional on `T/W`, so it is a line of `R/W = Pi`. The three `h` extend
  to a common functional on `Pi` iff `f(x) + f(y) = f(x+y)`, and this happens
  iff the `F(T)` have a common extension to `R`.
* If some point of `Pi` is not in `S`, that point carries an independent
  uniform bit, so the test rejects with probability exactly `1/2`.

By the union bound, and because each of `x`, `y`, `x+y` is uniform on
`Q \ 0`,

    E rej(f) <= t_W + (1/2) * 3 eps_W.

Since `min_psi D_W(psi) <= dist(f) <= rej(f)` for every realisation, it also
holds in expectation:

    min_psi D_W(psi) <= t_W + 1.5 eps_W.   (BLR-W)

## Step 4: Theorem S

Averaging (BLR-W) over `W` and using Step 2,

    Dmin <= t + 1.5 eps <= 5.5 eps <= 5.5 (1 - val),

where the last step uses Step 0.

Suppose `val >= 1/2 + gamma`. Then `1 - val <= 1/2 - gamma`, so
`Dmin <= 5.5(1/2 - gamma)`. This is at most `gamma - gamma'` iff
`gamma >= (2.75 + gamma')/6.5`, that is iff
`val >= (6 + gamma')/6.5`. Take `Psi` to be all functionals. `[]`

## Step 5: Theorem G, gluing along Grassmann edges

For each `W`, fix a minimiser `psi_W` of `D_W` among the extensions of
`F(W)`, and put `d := E_W D_W(psi_W)`. By Step 4, `d <= 5.5 eps`.

**Adjacent references agree.** Let `(W, W')` be a uniform ordered pair of
distinct `(l-1)`-spaces with `U := W cap W'` of dimension `l-2`. This is a
uniform edge of the Grassmann graph `J_2(n, l-1)`. Let `u` be uniform and put

    T1 := W + u,   T2 := W' + u,   W'' := U + u.

Call the draw *good* if all of the following hold:

* (i) `u notin W + W'`;
* (ii) `(W, T1)` is satisfied and `F(T1)(u) = psi_W(u)`;
* (iii) `(W', T2)` is satisfied and `F(T2)(u) = psi_W'(u)`;
* (iv) `(W'', T1)` and `(W'', T2)` are satisfied.

On a good draw, (i) makes `T1` and `T2` into `l`-spaces and `W''` into an
`(l-1)`-space lying in both. Since `u` is in `W''`, (iv) gives
`F(T1)(u) = F(W'')(u) = F(T2)(u)`. So `psi_W(u) = psi_W'(u)`.

Bound the probability that each condition fails.

* (i) fails with probability `2^(l-n) = 2^(1-m)`.
* `(W,u)` is uniform, so (ii) fails with probability at most `eps + d`, and
  likewise for (iii).
* Given (i), the tuple `(U, u, w)` with `W = U + w` is a uniformly random
  `(l-2)`-space together with two vectors independent modulo it. So
  `(W'', T1) = (U + u, U + u + w)` is a uniform edge, and likewise
  `(W'', T2)`. Hence each part of (iv) fails with probability at most `eps`.

So `Pr[not good] <= 2^(1-m) + 4 eps + 2d`.

Put `delta := psi_W - psi_W'`. If `delta != 0`, then `delta(u) = 1` with
probability `1/2` over `u`, and every such `u` gives a bad draw. So

    p := Pr_edge[psi_W != psi_W'] <= 2 Pr[not good] <= 8 eps + 4 d + 2^(2-m) <= 30 eps + 2^(2-m).

**Spectral gluing.** Let `A` be the normalised adjacency operator of the
Grassmann graph on `(l-1)`-spaces, with second-largest eigenvalue `lambda_2`.
For the classes `C_psi := {W : psi_W = psi}` with masses `mu_psi`, the
standard bound `<1_C, A 1_C> <= mu^2 + lambda_2 (mu - mu^2)` gives

    p = sum_psi (mu_psi - <1_C, A 1_C>) >= (1 - lambda_2) sum_psi mu_psi (1 - mu_psi) >= (1 - lambda_2)(1 - max_psi mu_psi).

*Import (spectrum).* The Wikipedia article "Grassmann graph" states,
verbatim: "The characteristic polynomial of J_q(n,k) is given by
φ(x):=∏[j=0 to diam(J_q(n,k))](x−(q^(j+1)[k−j]_q[n−k−j]_q−[j]_q))^((n choose j)_q−(n choose j-1)_q)".
It cites Brouwer, Cohen and Neumaier, *Distance-Regular Graphs*, Springer
1989 (Thm 9.3.3 there).

With `q = 2` and `k = l-1`, write `a = [k-1]`, `b = [n-k-1]`. Then
`[k] = 2a+1` and `[n-k] = 2b+1`, which gives:

* `theta_0 = 2(2a+1)(2b+1) = 8ab + 4a + 4b + 2`;
* `theta_1 = 4ab - 1`.

So `2 theta_1 < theta_0`, which gives `lambda_2 = theta_1/theta_0 < 1/2`.
The eigenvalues `theta_j` decrease in `j`, so `theta_1` is the second
largest. `check_stability.py` confirms the closed form against the numeric
spectrum for `(n, k) = (4,1), (5,1), (5,2), (4,2)`.

Hence `1 - max mu_psi < 2p <= 60 eps + 2^(3-m)`. Let `psi*` be a heaviest
class. Then

    E_W D_W(psi*) <= d + Pr_W[psi_W != psi*] <= 5.5 eps + 60 eps + 2^(3-m) = 65.5 eps + 2^(3-m).

For (GStar_n) with `Psi = {psi*}`, we need `65.5 (1/2 - gamma) + 2^(3-m) <= gamma - gamma'`.
This holds iff `val >= (66 + gamma' + 2^(3-m))/66.5`. `[]`

## Remarks

* **The constants.** The factor 4/3 of Lemma F7 is attained, so any
  improvement of the 0.923 threshold must change Step 2 or Step 3 as a
  whole. Local Fano accounting alone cannot do it.
* **Uniformity.** No step depends on `n` or `l` except through `2^(1-m)`
  and `2^(3-m)` in Theorem G.
* **Scope.** Theorem G is the per-labelling statement. Its use as (Star-List)
  goes through the image-determined transfer in the proof of LS\* of
  `list-star-coherent-selector-witnesses-put-np-in-rp`, which is not redone
  here.
