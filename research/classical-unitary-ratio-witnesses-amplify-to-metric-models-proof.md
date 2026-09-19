---
rg: 2
id: classical-unitary-ratio-witnesses-amplify-to-metric-models-proof
kind: route
title: Convolve the eigenvalue measure of the witnessed element, using a balanced replica against trace rotation and a parity bound against rank cancellation
target: classical-unitary-ratio-witnesses-amplify-to-metric-models
requires:
  - balanced-replica-hs-amplification
  - thompson-v-finitely-presented-infinite-simple
artifacts:
  - experiments/ratio-witness-amplification-2026-09-17/check_amplification.py
  - experiments/ratio-witness-amplification-2026-09-17/output.txt
---

Throughout, `X = r(U)` for a relator `r in R_0`, `A = a(U)`, and all three lengths are those of the claim.

## 0. Two general facts

**(T) Telescoping.** For a unitary `X in U(d)` and `k >= 1`,

```text
X^(tensor k) - I = sum_(i=1..k) I^(tensor (i-1)) tensor (X - I) tensor X^(tensor (k-i)).
```

Each summand is `X - I` tensored with unitaries. That multiplies the operator norm by `1` and the normalized HS norm by `1`,
and multiplies the rank by `d^(k-1)`, so normalized rank is unchanged. Hence

```text
l(X^(tensor k)) <= k l(X)      for l in {l_op, l_2, l_rk}.
```

**(E) Eigenvalue measures.** Diagonalize `A` in an orthonormal basis, `A = diag(e^(i theta_1), ..., e^(i theta_d))`. Write
`mu_A = (1/d) sum_j delta_(theta_j)`, a probability measure on the circle `T = R/2 pi Z`, written additively. Then
`A^(tensor k)` is diagonal in the product basis, with eigenvalues `e^(i(theta_(j_1)+...+theta_(j_k)))`, so

```text
mu_(A^(tensor k)) = mu_A^(*k).
```

In particular `tau(A^(tensor k)) = tau(A)^k`, and `1 - l_rk(A^(tensor k)) = mu_A^(*k)({0})`.

## 1. Operator norm

Put `t = l_op(A)`, which is positive because `A != I`, and at most `2`. Some eigenvalue `e^(i theta)`, with
`|theta| <= pi`, has `2|sin(theta/2)| = t`, so `|theta| >= t`. Let `k = ceil(pi/(2|theta|))`. Then

```text
k|theta| in [pi/2, pi/2 + |theta|] <= [pi/2, 3pi/2],
```

so `A^(tensor k)` has the eigenvalue `e^(ik theta)` with `|e^(ik theta) - 1| >= sqrt 2`. By (T),

```text
l_op(X^(tensor k)) <= k epsilon t <= (pi/(2t) + 1) epsilon t <= (pi/2 + 2) epsilon <= 4 epsilon.
```

## 2. Hilbert--Schmidt

Put `s = l_2(A)^2 = 2 - 2 Re tau(A)`, with `0 < s <= 4`, and `tau(A) = rho e^(i phi)` where `rho = |tau(A)| <= 1`.

**Case 1: `rho <= 1 - s/8`.** Let `k = ceil(8/s)` and `W = (U tensor conj U)^(tensor k)`. By
`balanced-replica-hs-amplification` (with `V = I`, `B(I) = I`),

```text
tau(a(W)) = |tau(A)|^(2k) <= rho^k <= (1 - s/8)^k <= e^(-ks/8) <= e^-1,
l_2(r(W))^2 <= 2k l_2(X)^2 <= 2(8/s + 1) epsilon^2 s = (16 + 2s) epsilon^2 <= 24 epsilon^2.
```

So `l_2(a(W))^2 = 2 - 2 tau(a(W)) >= 2(1 - e^-1)`, and `l_2(r(W)) <= 5 epsilon`. The map
`g -> (g tensor conj g)^(tensor k)` is a continuous homomorphism `U(d) -> U(d^(2k))`.

**Case 2: `rho > 1 - s/8`.** Here `rho > 1/2`, and `rho cos phi = Re tau(A) = 1 - s/2`. So

```text
cos phi = (1 - s/2)/rho < (1 - s/2)/(1 - s/8) = 1 - (3s/8)/(1 - s/8) <= 1 - 3s/8.
```

Since `1 - cos phi <= phi^2/2`, taking `|phi| <= pi` gives `|phi| >= sqrt(3s/4) > 0`. Let `k = ceil(pi/(2|phi|))` and
`W = U^(tensor k)`. Then `k|phi| in [pi/2, 3pi/2]`, so

```text
Re tau(a(W)) = rho^k cos(k phi) <= 0,        l_2(a(W))^2 >= 2.
```

Also `k <= pi/(2 sqrt(3s/4)) + 1 <= 2/sqrt s + 1`, so by (T)

```text
l_2(r(W)) <= k epsilon sqrt s <= 2 epsilon + epsilon sqrt s <= 4 epsilon.
```

## 3. Rank

Put `delta = l_rk(A)`. It is positive, and `A` is diagonalizable, so `mu_A({0}) = 1 - delta`.

If `delta >= 1/2`, take `k = 1`: then `l_rk(a(U)) >= 1/2` and `l_rk(r(U)) <= epsilon`.

Now let `delta < 1/2` and write `mu_A = q delta_0 + p nu` with `p = delta` and `q = 1 - delta`. Here `nu` is a probability
measure with `nu({0}) = 0`. Binomial expansion in the commutative convolution algebra gives

```text
mu_A^(*k)({0}) = S := sum_(j=0..k) b_j p_j,     b_j = C(k,j) p^j q^(k-j),     p_j = nu^(*j)({0}),
```

with `p_0 = 1`.

**Parity bound.** `p_j + p_(j+1) <= 1` for every `j`. Indeed `nu` is carried by the finite set of nonzero angles, and
`nu^(*j)({-x}) <= nu^(*j)(T \ {0}) = 1 - p_j` for `x != 0`, so

```text
p_(j+1) = sum_(x != 0) nu^(*j)({-x}) nu({x}) <= 1 - p_j.
```

**Summation.** Put `M = max_j b_j`. Pair consecutive terms:

```text
2S = b_0 + b_k p_k + sum_(j=0..k-1) (b_j p_j + b_(j+1) p_(j+1))
   <= b_0 + b_k + sum_(j=0..k-1) max(b_j, b_(j+1)),
```

because `b_j p_j + b_(j+1) p_(j+1) <= max(b_j, b_(j+1)) (p_j + p_(j+1))`. The binomial pmf is unimodal, since
`b_(j+1)/b_j` is decreasing in `j`. So `sum_(j=0..k-1) |b_j - b_(j+1)| = 2M - b_0 - b_k`, and then

```text
sum_(j=0..k-1) max(b_j, b_(j+1)) = (1/2) sum (b_j + b_(j+1) + |b_j - b_(j+1)|) = 1 + M - b_0 - b_k.
```

Hence `S <= (1 + M)/2`.

**Maximum of the binomial pmf.** By Fourier inversion,
`b_j = (1/2 pi) int_(-pi..pi) (q + p e^(it))^k e^(-ijt) dt`. Also

```text
|q + p e^(it)|^2 = 1 - 2pq(1 - cos t) <= exp(-4pq t^2 / pi^2)      for |t| <= pi,
```

using `1 - cos t >= 2t^2/pi^2`. Therefore

```text
M <= (1/2 pi) int_R exp(-2kpq t^2/pi^2) dt = sqrt(pi / (8kpq)).
```

**Choice of `k`.** Let `k = ceil(pi/delta)`. Since `q > 1/2`, `M <= sqrt(pi/(4k delta)) <= 1/2`, so `S <= 3/4` and

```text
l_rk(a(U^(tensor k))) = 1 - S >= 1/4.
```

By (T), `l_rk(r(U^(tensor k))) <= k epsilon delta <= (pi + delta) epsilon <= 4 epsilon`.

This completes (A).

The script `experiments/ratio-witness-amplification-2026-09-17/check_amplification.py` checks the rank inequalities
`S <= (1+M)/2`, the Fourier bound on `M` and `S <= 3/4` by exact convolution. It includes the adversarial measure
`nu = delta_pi`, the eigenvalue `-1`, where cancellation is maximal and `S -> 1/2`. It also checks the Hilbert--Schmidt
case split on random spectra. The output is in `output.txt` next to it. This is a sanity check, not part of the proof.

## 4. Part (B)

Each of the three lengths is conjugation invariant, symmetric and subadditive on `U(d)`. For rank this is
`rank(gh - I) <= rank(g(h - I)) + rank(g - I)`. So for every sequence `(d_m)` and every ultrafilter `omega`,

```text
N_l = { (g_m) : l(g_m) -> 0 along omega }
```

is a normal subgroup of `prod_m U(d_m)`.

**Witness to homomorphism.** Enumerate `R` as an increasing union of finite sets `R_1 <= R_2 <= ...`. Take a witness `U_m`
for `R_m` and `epsilon = 1/m`, and amplify it by (A) to `W_m`. For a nonprincipal `omega`, the assignment
`s -> [(W_m(s))_m]` defines a homomorphism `F(S) -> prod_omega U(d'_m)/N_l`.

- Every `r in R` lies in `R_m` for large `m`, and `l(r(W_m)) <= 5/m`, so `r` maps to `1` and the map factors through `Gamma`.
- `l(a(W_m))` is bounded below by `min(sqrt 2, sqrt(2(1 - e^-1)), 1/4) > 0`, so `a` does not map to `1`.

**Homomorphism to witness.** Let `psi` be a homomorphism with `psi(a) != 1`, and lift the generators to sequences
`(U_m(s))_m`. Then `l(r(U_m)) -> 0` along `omega` for each `r`. Also some `c > 0` has `l(a(U_m)) >= c` on an
`omega`-large set, because otherwise `psi(a)` would lie in `N_l`. Given `R_0` finite and `epsilon > 0`, intersect finitely
many `omega`-large sets to find `m` with `max_(r in R_0) l(r(U_m)) < epsilon c <= epsilon l(a(U_m))`.

## 5. Part (C)

`V` is simple (`thompson-v-finitely-presented-infinite-simple`), so any homomorphism from `V` that does not kill `a` is
injective. By (B), an `l`-ratio witness for one `a != 1` is therefore the same as an embedding of `V` into the
corresponding ultraproduct.

**Operator norm.** This is the MF property of `countable-group-mf-conventions`, the unitary-sequence corona definition.

- Enumerate `V = {g_1, g_2, ...}` and let `c_i` be the separation of `g_i != 1` in the ultraproduct.
- For each `n`, pick one index `m_n` in the `omega`-large set where the multiplication defects of `g_i g_j`, for
  `i, j <= n`, are below `1/n`, and `l_op(phi_m(g_i)) > c_i/2` for `i <= n`.
- The sequence `(phi_(m_n))_n` then embeds `V` in `prod_n U(d_(m_n)) / {l_op -> 0}`.

The converse, from the corona to a witness, is the same argument as in (B), using `limsup` in place of `omega`.

**Hilbert--Schmidt.** An embedding in a tracial ultraproduct of the `U(d_m)` is the definition of hyperlinearity used in
`thompson-v-hyperlinear`.

**Rank.** The inclusion `U(d) <= GL_d(C)` preserves normalized `rank(g - h)`. So it induces an injective homomorphism of
the rank ultraproducts, and an embedding of `V` in the unitary one is an embedding in the `GL_d(C)` one: `V` is linear
sofic over `C`.

No other input is used. The two required claims are ESTABLISHED.
