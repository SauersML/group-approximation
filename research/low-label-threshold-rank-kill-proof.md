---
rg: 2
id: low-label-threshold-rank-kill-proof
kind: route
title: The completing labeling is a unit vector of Rayleigh quotient 1-eps for the label-extended walk; greedy Gram-Schmidt on the columns of a walk power captures it in dimension 2R, and a grid there rounds by argmax
target: low-label-threshold-rank-reductions-cannot-prove-ugc
requires: []
artifacts:
  - experiments/ugc-label-rank-kill-2026-09-17/check_label_rank_kill.py
---

Notation is as in the target claim. Only finite-dimensional linear algebra is
used: the spectral theorem for symmetric real matrices, and the fact that the
sum of the `m x m` principal minors of a symmetric matrix is the `m`-th
elementary symmetric function of its eigenvalues. The latter is the coefficient
identity of the characteristic polynomial. Put `n = Nk` and
`<g, h> = sum_(z in V x [k]) pi_L(z) g(z) h(z)`, with `||g||^2 = <g, g>`.

## (0) The walk is stochastic and self-adjoint

For `e` between `u` and `v`, `sigma_e^(u->v)` is `sigma_e` if `e = (u, v, ...)`
and its inverse otherwise. Row `(u, a)` of `A_L` sums to
`sum_(e at u) w_e / deg(u) = 1`, since each edge sends `a` to exactly one
label. Also
`pi_L(u,a) A_L((u,a),(v,b)) = sum_e (w_e / 2W) 1[b = sigma_e^(u->v)(a)]`.
This is symmetric under `(u,a) <-> (v,b)`, because
`b = sigma_e^(u->v)(a)` iff `a = sigma_e^(v->u)(b)`. So
`Pi A_L = A_L^T Pi` with `Pi = diag(pi_L)`, and
`S_L = Pi^(1/2) A_L Pi^(-1/2)` is a real symmetric matrix similar to `A_L`. The
eigenvalues are real and lie in `[-1, 1]`, since `A_L` is stochastic. There is
a `<.,.>`-orthonormal eigenbasis (`phi = Pi^(-1/2) psi` for orthonormal
eigenvectors `psi` of `S_L`). The same holds for
`B = (I + A_L)/2`, whose eigenvalues are `(1 + lambda)/2 in [0, 1]`, and for
the constraint walk `A(u, v) = sum_(e between u, v) w_e / deg(u)` in `L2(pi)`.

## (1) Rayleigh identity

Let `f(u, a) = 1[a = x_u]`. Then `||f||^2 = sum_u pi(u) = 1`, and
`<f, A_L f> = sum_u pi(u) sum_(e at u) (w_e / deg(u)) 1[x_v = sigma_e^(u->v)(x_u)]`
`= sum_u sum_(e at u) (w_e / 2W) 1[e satisfied]`. Each edge is counted once
from each endpoint, and satisfaction is symmetric, so this is `val(x)`. Hence
`<f, B f> = (1 + val(x)) / 2`.

## (2) Spectral split

Let `M` be self-adjoint in `<.,.>` with eigenvalues `<= 1`, and let
`theta < 1`. Write `g = g_hi + g_lo`, where `g_hi` is the projection onto the
span of the eigenvectors with eigenvalue `>= theta`. The two parts are
orthogonal and `M`-orthogonal. So
`<g, M g> <= ||g_hi||^2 + theta ||g_lo||^2 = ||g||^2 - (1 - theta) ||g_lo||^2`.
For `g = f` and `M = B`:
`||f_lo||^2 <= (1 - <f, B f>) / (1 - theta) = (1 - val(x)) / (2 (1 - theta))`.

## (3) Rounding

For `g : V x [k] -> Q` let `x_g(u)` be the least `a` maximizing `g(u, a)`. Let
`S = {u : x_g(u) != x_u}`.

*Claim:* `pi(S) <= 2 ||g - f||^2` and `val(x_g) >= val(x) - 4 ||g - f||^2`.

Fix `u in S`, with `a = x_u` and `b = x_g(u) != a`, and put
`p = g(u, a)`, `q = g(u, b) >= p`. Then
`sum_c (g - f)(u, c)^2 >= (1 - p)^2 + q^2`.
- If `p <= 0`, this is `>= 1`.
- If `p > 0`, then `q^2 >= p^2`, and `(1 - p)^2 + p^2 >= 1/2`.

Multiplying by `pi(u)` and summing over `S`,
`||g - f||^2 >= pi(S) / 2`. An edge satisfied by `x` and not by `x_g` has an
endpoint in `S`. The weight of edges at `S` is at most
`sum_(u in S) deg(u) = 2W pi(S)`. So
`val(x_g) >= val(x) - 2 pi(S) >= val(x) - 4 ||g - f||^2`.

## (4) Parameters and the algorithm

Fix `eps in (0, 1/800]` and put `gamma = 400 eps <= 1/2`,
`theta_hi = 1 - gamma/8`, `delta = 1/100`, `eta = 9/100`. Let
`L = ceil(log2(2nW))`. Every `u` has `deg(u) >= 1`, so
`n / pi_min <= 2nW <= 2^L`. Put `tau = 2^(-30 - 6L)` and
`t = ceil(0.7 (30 + 7L) / gamma)`. Let
`R = rank_(1-800eps)(A_L)`. Since `lambda_B = (1 + lambda)/2`, `R` is the
number of eigenvalues of `B` that are `>= 1 - gamma`.

*Algorithm.*

1. Compute `P = B^t` exactly. Its columns are `w_z = P 1_z` for
   `z in V x [k]`.
2. Start with the empty list `v_1, ..., v_i` (`i = 0`) and repeat. For every
   `z`, compute the residual `res_z = w_z - sum_(l <= i) (<w_z, v_l> / <v_l, v_l>) v_l`.
   - If `max_z ||res_z||^2 <= tau`, stop and go to step 3.
   - If `i = 2R*`, stop with "rank above `R*`".
   - Otherwise let `v_(i+1) = res_z` for the least maximizing `z`, and repeat.
3. Let `m = i`. For each `l`, let `e_l` be the integer with
   `4^(e_l) <= ||v_l||^2 < 4^(e_l + 1)`, and put `psi_l = 2^(-e_l) v_l`, so
   `1 <= ||psi_l|| < 2`.
4. Let `h = 2^(-ceil(log2(sqrt(m + 1) / eta)))`, so `h <= eta / sqrt(m + 1)`.
   Let `Lev = {-1 + jh : 0 <= j <= ceil(2/h)}`.
5. For every `d in Lev^m`, form `g_d = sum_l d_l psi_l`, round it by (3), and
   compute the value. Output the best labeling found.

The `v_l` are pairwise orthogonal by construction. `res_z` is `Q w_z`, where `Q`
is the `<.,.>`-orthogonal projection onto the orthogonal complement of
`T' = span(v_1, ..., v_i)`.

## (5) Greedy selection stops by dimension 2R

*Claim:* if Gram--Schmidt residuals `v_1, ..., v_m` of distinct columns
`w_(z_1), ..., w_(z_m)` all satisfy `||v_l||^2 > tau`, then
`m <= max(2R - 1, 0)`.

*Gram determinant.* Let `G = (<w_(z_i), w_(z_l)>)_(i,l)`. Gram--Schmidt is a
unit lower triangular change of basis, so `det G = prod_l ||v_l||^2 > tau^m`.

*Principal minor.* By (0), `Pi P = P^T Pi`. So
`G_(il) = (P^T Pi P)_(z_i z_l) = (Pi P^2)_(z_i z_l)`. With `J = {z_1, ..., z_m}`,
`det G = prod_(z in J) pi_L(z) det((P^2)_(J,J))`, and
`det((P^2)_(J,J)) = det((S_B^(2t))_(J,J))` for the symmetric
`S_B = Pi^(1/2) B Pi^(-1/2)`, since conjugating by a diagonal matrix preserves
principal minors. `S_B^(2t)` is positive semidefinite with eigenvalues
`mu_i = lambda_(B,i)^(2t) in [0, 1]`. Since `pi_L <= 1`, `det G` is at most
the sum of all `m x m` principal minors of `S_B^(2t)`, which is `e_m(mu)`.

*Eigenvalue count.* Put `nu = (1 - gamma)^(2t)`. At most `R` of the `mu_i` are
`>= nu`. A product of `m` of them is `<= nu^(m - R)` when `m >= R`. So
`e_m(mu) <= binom(n, m) nu^(m - R) <= n^m nu^(m - R)`. Also
`nu <= exp(-2 gamma t) <= exp(-2 ln(n / tau)) = tau^2 / n^2`. This uses
`gamma t >= 0.7 (30 + 7L) >= ln 2 (L + 30 + 6L) >= ln(n / tau)`.

*Contradiction.*
- If `R >= 1` and `m >= 2R`, the first `2R` residuals give
  `tau^(2R) < n^(2R) nu^R <= tau^(2R)`.
- If `R = 0` and `m >= 1`, the first residual gives `tau < n nu <= tau^2 / n < tau`.

*Consequences.*
- If `R <= R*`, step 2 never stops with "rank above `R*`". At that stop
  `2R*` residuals exceed `tau` and so does one more, so by the claim
  `2R* + 1 <= max(2R - 1, 0)`, which forces `R >= R* + 1`.
- Stopping with "rank above `R*`" certifies `R > R*`.
- At the ordinary stop, `m <= 2R*` and `||Q w_z||^2 <= tau` for every `z`.

## (6) The completing labeling is near a grid point

Let `val(x) >= 1 - eps` and suppose step 2 reached step 3. Split
`f = f_hi + f_lo` along the eigenvalues of `B` at `theta_hi`.

*Low part.* By (2),
`||f_lo||^2 <= (1 - val(x)) / (2 gamma / 8) <= 4 eps / (400 eps) = 1/100`.

*High part.* Write `f_hi = sum_phi c_phi phi` over orthonormal eigenvectors with
`lambda_phi >= theta_hi > 0`, and put `p = sum_phi c_phi lambda_phi^(-t) phi`.
Then `P p = f_hi` and `||p|| <= theta_hi^(-t)`. By Cauchy--Schwarz,
`sum_z |p(z)| <= ||p|| (sum_z 1/pi_L(z))^(1/2) <= 2^(L/2) theta_hi^(-t)`. Since
`f_hi = sum_z p(z) w_z`,
`||Q f_hi|| <= sum_z |p(z)| ||Q w_z|| <= 2^(L/2) theta_hi^(-t) tau^(1/2)`.

*Numbers.* `-ln(1 - y) <= 2y` for `y <= 1/2` gives
`theta_hi^(-t) <= exp(gamma t / 4) <= exp(0.175 (30 + 7L) + 1/4)`. With
`exp(y) <= 2^(1.443 y)`, this is `<= 2^(0.2526 (30 + 7L) + 0.361)`. So
`log2 ||Q f_hi|| <= L/2 + 0.2526 (30 + 7L) + 0.361 - 15 - 3L`
`= -0.7318 L - 7.061 < log2(1/100) = -6.64`, and `||Q f_hi|| <= delta`.

*Projection.* So `||f - (I - Q) f|| = ||Q f|| <= delta + 1/10`. Write
`(I - Q) f = sum_l c_l psi_l` with `c_l = <f, psi_l> / ||psi_l||^2`. Then
`|c_l| <= ||f|| / ||psi_l|| <= 1`. Choose `d_l in Lev` with
`|c_l - d_l| <= h/2`. Orthogonality gives
`||(I - Q) f - g_d||^2 = sum_l (c_l - d_l)^2 ||psi_l||^2 <= m (h^2 / 4) 4 <= eta^2`.

*Value.* So `||g_d - f|| <= eta + delta + 1/10 = 1/5`, and by (3) the output
has value `>= val(x) - 4/25 = val(x) - 0.16 >= 1 - eps - 0.16`.

## (7) Bit complexity

Cap the cutoff at `R* <= n`, since `R <= n`. Weights are positive integers.

*Entries of P.* Write `A_L = D^(-1) W_L`, where `W_L` has integer entries
`sum_e w_e 1[...]` and `D = diag(deg(u))`. Then `B = (2D)^(-1) (D + W_L)`, and
`Delta^t P` is an integer matrix with entries in `[0, Delta^t]`, where
`Delta = lcm_u 2deg(u) <= (2W)^N`. Put `[y, y'] = 2W <y, y'>`, an integer form
with weights `deg(u) >= 1`. Replace the columns by `y_z = Delta^t w_z` and
`tau` by `2W Delta^(2t) tau`, measuring norms with `[.,.]`. Every residual
scales by `Delta^t` and every squared norm by `2W Delta^(2t)`, so the run and
its decisions are unchanged. The integer
`K = 2Wn Delta^(2t)` bounds every `[y_z, y_z]`, and
`log2 K <= log2(2Wn) + 2tN log2(2W)`, which is `poly(Z, 1/eps)` because
`t = O(L / eps)`.

*Gram--Schmidt sizes.* Let `v` be the residual of an integer vector `y` against
the span of independent integer vectors `y_1, ..., y_i` with Gram matrix `G_i`,
`D_i = det G_i >= 1`. Then `v = y - sum_l alpha_l y_l` with
`G_i alpha = ([y, y_l])_l`, and Cramer's rule makes `D_i v` an integer vector.
We have `v(z)^2 <= [v, v] <= [y, y] <= K`, and
`D_i = prod_l [v_l, v_l] <= K^i` by (5). So every entry of every residual is a
fraction whose numerator and denominator have at most `(i + 1) log2 K` bits.
The coefficients `[y, v_l] / [v_l, v_l]` have `[v_l, v_l] = D_l / D_(l-1)`, and
`D_(l-1) [y, v_l]` is an integer of absolute value `<= n K^(l+1)`.

So all numbers have `poly(Z, 1/eps)` bits, and reduced-fraction arithmetic is
polynomial. Step 2 runs at most `2R* + 1 <= 2n + 1` rounds of `n` residuals of
at most `2R*` terms. The integers `e_l` and `h` have polynomially many bits.
Step 5 evaluates `|Lev|^m` grid points in polynomial time each, with
`m <= 2R*` and `|Lev| <= 2/h + 2 <= 4 sqrt(2R* + 1) / eta + 2`. The total time
is `poly(Z, 1/eps) (4 sqrt(2R* + 1) / 0.09 + 2)^(2R*)`. With (5) and (6) this
proves Theorem 1.

## (8) Twisted trace certificate

The diagonal entry `A_L^(2t)((u,a),(u,a))` is a sum over edge sequences
`e_1, ..., e_(2t)` forming closed walks `u = u_0, u_1, ..., u_(2t) = u`, of
`prod_i w_(e_i) / deg(u_(i-1))` times `1[H(a) = a]`, where
`H = sigma_(e_(2t))^(u_(2t-1) -> u) o ... o sigma_(e_1)^(u -> u_1)` is the
holonomy. The diagonal entry `A^(2t)(u, u)` is the same sum without the
indicator. `H` has at most `k` fixed points, so summing over `a` and `u` gives
`Tr(A_L^(2t)) <= k Tr(A^(2t))`.

The eigenvalues of `A_L` are real by (0), so
`Tr(A_L^(2t)) = sum lambda^(2t) >= rank_theta(A_L) theta^(2t)` for
`theta > 0`.

If `A` (real spectrum in `[-1, 1]` by (0)) has at most `r0` eigenvalues with
`|mu| > 1 - gamma0`, then `Tr(A^(2t)) <= r0 + N (1 - gamma0)^(2t) <= r0 + 1`
for `t = ceil(ln N / 2gamma0)`. With `theta = 1 - 800 eps` and
`800 eps <= 1/2`, `theta^(-2t) <= exp(3200 eps t)`. This proves Theorem 2.

## (9) Class kill

Let `Red` map 3SAT formulas `phi` to unique games `Red(phi)` of size `Z` in
polynomial time. YES formulas map to games of value `>= 1 - eps`, and NO
formulas to games of value `<= s`, with `eps <= 1/800` and `s < 0.84 - eps`.
Given a cutoff function `R*(Z)`, decide `phi` as follows.
- Run Theorem 1 on `Red(phi)` with `R*(Z)`.
- On "rank above `R*`", answer NO.
- Otherwise answer YES iff the output labeling has value `> s`.

*Correctness.* Suppose every YES output has `rank_(1-800eps)(A_L) <= R*(Z)`. A
YES `phi` never gets "rank above" by (5), and gets a labeling of value
`>= 0.84 - eps > s` by (6). For a NO `phi`, every labeling has value `<= s`,
and "rank above" also answers NO.

*Time.* It is `poly(Z) exp(O(R* log(R* + 1)))`.
- `R* = c log Z / log log Z` gives `poly(Z) Z^(O(c))`, so `P = NP`.
- `R* = (log Z)^c` gives `exp(O((log Z)^c log log Z))`, which is
  quasi-polynomial.
- *ETH.* ETH states that for some `delta0 > 0`, 3SAT on `n` variables has no
  `2^(delta0 n)`-time algorithm. Let `Z <= n^A`, and suppose some
  `alpha < 1/A` has only finitely many YES outputs with rank `> Z^alpha`. Take
  `R* = Z^alpha <= n^(A alpha)`, and answer the finitely many exceptional
  formulas from a table. The time is `exp(O(n^(A alpha) log n)) = 2^(o(n))`,
  contradicting ETH.

Every step used the completeness promise only. This proves Theorem 3.
