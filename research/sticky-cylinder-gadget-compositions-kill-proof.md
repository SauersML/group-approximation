---
rg: 2
id: sticky-cylinder-gadget-compositions-kill-proof
kind: route
title: Edge-measure pushforward preserves expansion of preimages, and arity cylinders of projection games return with probability 1/k, so fibred compositions keep non-expanding sets at every scale
target: sticky-cylinder-gadget-compositions-cannot-prove-sseh
requires: []
artifacts:
  - experiments/fibred-sse-kill-2026-09-17/check_fibred_kill.py
---

Notation is as in the target claim. All chains are finite and reversible, and
`E_O(S, T) = sum_(u in S, v in T) mu(u) O(u, v)` is symmetric. Because `O` is
stochastic, `E_O(S, V) = mu(S)`, and hence
`1 - Phi_O(S) = E_O(S, S) / mu(S)`.

## (0) Sticky sets do not expand

If `A` is c-sticky, then
`E_O(A, A) = sum_(v in A) mu(v) O(v, A) >= c mu(A)`. So `Phi_O(A) <= 1 - c`.

## (1) Pullback

Put `E' = E_(G')` and `A' = pi^-1 A`. The pushforward identity
`(pi x pi)_* E' = E_O` says that `E'(pi^-1 S, pi^-1 T) = E_O(S, T)` for all
`S, T <= V`. Taking `T = V` gives `mu'(A') = E'(A', V') = E_O(A, V) = mu(A)`.
Taking `S = T = A` gives `E'(A', A') = E_O(A, A)`. Dividing,
`Phi_(G')(A') = Phi_O(A)`, and this is `<= 1 - c` by (0).

Fibrations compose: if `pi_1 : V'' -> V'` and `pi_2 : V' -> V` are fibrations,
then `((pi_2 pi_1) x (pi_2 pi_1))_* E'' = (pi_2 x pi_2)_* E' = E_O`.

## (2) Profile

Let `A_0 <= ... <= A_m` be the ladder and fix `delta in (0, 1]`. Let `j` be the
least index with `mu(A_j) >= delta`. It exists because `mu(A_m) = 1`, and
`j >= 1` because `mu(A_0) = 0`. Minimality gives `mu(A_(j-1)) < delta`, so
`mu(A_j) < delta + varsigma`. By (1), `S' = pi^-1 A_j` has
`mu'(S') in [delta, delta + varsigma]` and `Phi_(G')(S') <= 1 - c`.

*Exact volume.* Now let `G'` be regular, so `mu'` is uniform on `n = |V'|`
points, and let `delta n` be an integer. Then `|S'| >= delta n`. Choose
`T <= S'` with `|T| = delta n`, and let `D = S' \ T`, with
`mu'(D) <= varsigma <= varsigma'`. Every ordered pair of `S' x S'` that is not
in `T x T` has a coordinate in `D`. So
`E'(S', S') - E'(T, T) <= E'(D, V') + E'(V', D) = 2 mu'(D)`. Hence
`E'(T, T) >= c mu'(S') - 2 varsigma' >= c delta - 2 varsigma'`, and
`1 - Phi_(G')(T) = E'(T, T) / delta >= c - 2 varsigma' / delta`.

## (3) Bounded-arity projection games

Write `W(u, x) >= 0` for the edge weights on `L x R`,
`w_u = sum_x W(u, x)`, `vol(x) = sum_u W(u, x)`, `W_tot = sum_u w_u` and
`Z = 2 W_tot`. Vertices of zero volume are dropped. Then `mu(u) = w_u / Z`,
`mu(x) = vol(x) / Z`, `P(u, x) = W(u, x) / w_u`, `P(x, u) = W(u, x) / vol(x)`,
and `E_P(u, x) = W(u, x) / Z`. The hypothesis is

(H) `W(u, x) > 0` implies `W(u, x) >= w_u / k`.

In particular each `u` has at most `k` neighbours. Put
`N(X) = { u : W(u, X) > 0 }` and `A = X u N(X)`.

**(3.0) Powers of a sticky set.** If `A` is c-sticky for any chain `O`, then
`O^t(v, A) >= sum_(w in A) O(v, w) O^(t-1)(w, A) >= c min_(w in A) O^(t-1)(w, A)`.
By induction `O^t(v, A) >= c^t` for `v in A`.

**(3.1) One step.** If `x in X`, every neighbour of `x` lies in `N(X)`, so
`P(x, A) = 1`. If `u in N(X)`, then by (H) `P(u, X) >= 1/k`.

**(3.2) Powers `P^t`, pointwise.** Put `a_t = min_(x in X) P^t(x, A)` and
`b_t = min_(u in N(X)) P^t(u, A)`, so `a_0 = b_0 = 1`. Keeping only first steps
that land in `A`, (3.1) gives `a_t >= b_(t-1)` and `b_t >= a_(t-1) / k`. Hence
`b_t >= b_(t-2) / k`, with `b_1 >= 1/k` and `b_2 >= a_1 / k >= b_0 / k`. So
`b_t >= k^(-ceil(t/2))` and `a_t >= b_(t-1) >= k^(-ceil((t-1)/2))`. Therefore
`A` is `k^(-ceil(t/2))`-sticky for `P^t`, for every `t >= 1`.

**(3.3) The value for `t = 1`.** Put `a = sum_(u in N(X)) w_u` and
`b = sum_(u in N(X)) W(u, X)`. Every edge at `X` has its left end in `N(X)`, so
`b = vol(X)`. Then `mu(A) = (a + b) / Z`. The weight inside `A` comes from the
edges between `N(X)` and `X`, counted in both orders:
`E_P(A, A) = 2 b / Z`. So `1 - Phi_P(A) = 2b / (a + b)`, which increases in `b`.
By (H), `W(u, X) >= w_u / k` for `u in N(X)`, so `b >= a/k` and
`1 - Phi_P(A) >= 2/(k+1)`, that is `Phi_P(A) <= (k-1)/(k+1)`.

**(3.4) Even powers.** `P` is self-adjoint on `L^2(mu)`, with an orthonormal
eigenbasis `phi_i` and eigenvalues `lambda_i in [-1, 1]`. Let `nu` put mass
`<1_A, phi_i>^2 / mu(A)` at `lambda_i`. By Parseval `nu` is a probability
measure. Since `P^t` is reversible for `mu`,
`int lambda^t d nu = <1_A, P^t 1_A> / mu(A) = 1 - Phi_(P^t)(A)`. The function
`lambda -> lambda^(2s)` is convex, so Jensen gives
`1 - Phi_(P^(2s))(A) >= (1 - Phi_P(A))^(2s) >= (2/(k+1))^(2s)`, using (3.3).

**(3.5) One-sided walks.** Put `P_R(x, y) = sum_u P(x, u) P(u, y)` on `R`, with
`mu_R(x) = vol(x) / W_tot`. The edge measure
`mu_R(x) P_R(x, y) = sum_u W(u, x) W(u, y) / (w_u W_tot)` is symmetric. For
`x in X`, `P_R(x, X) = sum_(u in N(X)) P(x, u) P(u, X) >= 1/k`. Likewise
`P_L(u, v) = sum_x P(u, x) P(x, v)` on `L`, with `mu_L(u) = w_u / W_tot`. For
`u in N(X)`, `P_L(u, N(X)) >= sum_(x in X) P(u, x) P(x, N(X)) = P(u, X) >= 1/k`.
By (3.0), `X` and `N(X)` are `k^(-s)`-sticky for the `s`-th powers.

**(3.6) Ladders.** Enumerate `R = {x_1, ..., x_M}` and put `X_j = {x_1..x_j}`,
`A_j = X_j u N(X_j)`. Then `A_0` is empty and `A_M = L u R`, since every left
vertex of positive volume has a neighbour. By (H), `w_u <= k W(u, x)` for every
neighbour `u` of `x`, so
`mu(A_j) - mu(A_(j-1)) <= mu(x_j) + sum_(u ~ x_j) w_u / Z <= (k+1) mu(x_j)`,
which is at most `varsigma_B`. For `P_R`, the increment of `mu_R(X_j)` is
`2 mu(x_j) <= varsigma_B`. For `P_L`, the increment of `mu_L(N(X_j))` is at most
`k vol(x_j) / W_tot = 2k mu(x_j) <= 2 varsigma_B`.

**(3.7) Parallel repetition.** `B^r` has weights
`W^r(ubar, xbar) = prod_i W(u_i, x_i)`. Its walk moves the coordinates
independently, `P^r(ubar, xbar) = prod_i P(u_i, x_i)`. Its stationary measure is
`(1/2) prod_i mu_L(u_i)` on `L^r` and `(1/2) prod_i mu_R(x_i)` on `R^r`. Let `U`
be the union cylinder of `X`.

- If `xbar in U` with `x_i in X`, then the next `u_i` lies in `N(X)` surely.
- If `ubar in U` with `u_i in N(X)`, then `x_i in X` with probability
  `P(u_i, X) >= 1/k`.

So `U` is `1/k`-sticky. Its measure is
`(1/2)(1 - (1 - mu_L(N(X)))^r) + (1/2)(1 - (1 - mu_R(X))^r)`. The map
`p -> 1 - (1-p)^r` is `r`-Lipschitz on `[0, 1]`, and `mu_L = 2 mu` on `L`,
`mu_R = 2 mu` on `R`. So along `X_j` the increment is at most
`r (Delta mu(N(X_j)) + Delta mu(X_j)) = r Delta mu(A_j) <= r varsigma_B`. The
ladder starts at the empty set and ends at everything.

## (4) Closure

**Mixtures.** Let `O' = a O + (1-a) Q`, where `Q` is reversible for `mu`. Then
`E_(O') = a E_O + (1-a) E_Q` is symmetric with the same marginal `mu`, and
`O'(v, A) >= a O(v, A) >= a c`. For `Q(v, .) = mu` the bound is
`a c + (1-a) mu(A)`. The sets and measures do not change, so neither does the
step.

**Tensoring and gadget kernels.** Let `G'((v,z),(v',z')) = O(v,v') K_(v,v')(z,z')`
on `V' = { (v, z) }`, where each `K_(v,v')(z, .)` is a probability measure and
`mu'(v, z) = mu(v) nu_v(z)` with `sum_z nu_v(z) = 1`. Suppose `G'` is reversible
for `mu'`. Summing over `z, z'` gives `(pi x pi)_* E_(G') = E_O`, so `G'` is
fibred. Moreover `G'((v,z), pi^-1 A) = O(v, A) >= c` pointwise. The tensor
product `O (x) H` is the case `K_(v,v') = H`, `nu_v = mu_H`.

**Products.** In `O^(tensor r)` the coordinates move independently. If
`vbar in U_A` with `v_i in A`, then
`O^(tensor r)(vbar, U_A) >= O^(tensor r)(vbar, { w_i in A }) = O(v_i, A) >= c`.
The measure is `mu^(tensor r)(U_A) = 1 - (1 - mu(A))^r`, which is `r`-Lipschitz
in `mu(A)`. So the ladder `U_(A_j)` runs from the empty set to `V^r` with step
`<= r varsigma`. The coordinate cylinder `A x V^(r-1)` has constant `c` and
measure `mu(A)`.

**Folding by coordinate permutations.** Let `Gamma <= S_r` act on `V^r` by
permuting coordinates, and let `q` map a tuple to its orbit. `O^(tensor r)` and
`mu^(tensor r)` are `Gamma`-invariant. So
`Obar(q vbar, S) = O^(tensor r)(vbar, q^-1 S)` does not depend on the chosen
representative, `Obar` is reversible for `q_* mu^(tensor r)`, and
`E_Obar = (q x q)_* E_(O^(tensor r))`. The set `U_A` is `Gamma`-invariant, so
`q^-1 q U_A = U_A`. Hence `q U_A` is c-sticky for `Obar` and has the same
measure, and the ladder descends with the same step.

**Quotients along fibres.** Let `Gamma` act on `V'` preserving `G'` and `mu'`,
with `pi o gamma = pi`. The quotient chain `Gbar` on `V'/Gamma` has
`E_Gbar = (q x q)_* E_(G')`. The induced map `pibar` satisfies
`pibar o q = pi`, so
`(pibar x pibar)_* E_Gbar = (pi x pi)_* E_(G') = E_O`.

**Powers** are (3.0), and **composition** of fibrations is in (1).

## (5) Class kill

Let `x` be a NO instance and let `R(x) = G'` be fibred over `O`, where `O` has a
c-sticky ladder of step `varsigma = varsigma(x)`.

- Irregular convention. The NO case of `Gap-SSE(eta, delta)` requires
  `Phi(S) >= 1 - eta` for all `S` with `mu'(S) in [delta, 10 delta]`. If
  `varsigma <= 9 delta`, (2) gives such an `S` with `Phi(S) <= 1 - c < 1 - eta`.
- Regular graphs, exact volume. (2) gives `mu'(T) = delta` and
  `Phi(T) <= 1 - c + 2 varsigma'/delta < 1 - eta`.

In both cases `R(x)` is not a NO instance. A reduction must map NO instances to
NO instances, so `R` is not a reduction to `Gap-SSE(eta, delta)`. Only the
definition of a reduction is used.

**Instantiation.** For an outer game with (H) at arity `k`, built with walk
length `t`, laziness `a`, repetition `r` and folding as in (4), the output
has `c >= a k^(-ceil(t/2))` and `varsigma <= 2 r varsigma_B`. Here
`varsigma_B = (k+1) max mu(x)`, which tends to 0 when no right vertex carries
constant mass, as in any family of growing instances with bounded maximum
weight share. For such families the condition `varsigma <= 9 delta` holds once
instances are large enough at fixed `delta`. So every NO output fails
`Gap-SSE(eta, delta)` for `eta < a k^(-ceil(t/2))`.

## Replay

`experiments/fibred-sse-kill-2026-09-17/check_fibred_kill.py` runs 60 random
weighted projection games per seed and checks the following:

- (3.3) the bound `(k-1)/(k+1)`;
- (3.4) the Jensen inequality for `s = 1, 2, 3`;
- (3.5) the bound `k^(-s)` for `P_R^s` and `P_L^s`;
- the tensor-square coordinate cylinder, which matches `mu` and `Phi` to
  `1e-9`;
- (1) the pullback through a noisy-cube gadget over `P_R`;
- (3.6) the ladder increments against `varsigma_B`;
- (3.2) pointwise stickiness for `t = 1..5`, and the union cylinder of two
  `eps`-noised copies of `P_R` against `(1-eps)/k` (products plus mixtures).

It reports `FAILS 0` on seeds 20260917, 7 and 11, and the extremal violations
are at `1e-16`, so the bounds are attained.
