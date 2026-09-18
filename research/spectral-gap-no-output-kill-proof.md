---
rg: 2
id: spectral-gap-no-output-kill-proof
kind: route
title: Fourth-tensor embedding of a basic SDP solution has Dirichlet energy 4 eps; project onto the top r eigenspaces, cut by a random grid, and propagate labels from a root per cell through the >1/2 partial matchings
target: spectral-gap-no-outputs-cannot-prove-ugc
requires:
  - sdp-fixed-precision-solvable-gls
artifacts:
  - experiments/ugc-spectral-no-kill-2026-09-17/check_spectral_no_kill.py
---

Notation is as in the target claim. Only finite-dimensional linear algebra and
the imported solver theorem are used. Fix a feasible vector solution
`(u_a)` of the basic SDP in `R^d`, and write

```text
eps_e = 1 - sum_a <u_a, v_(sigma_e a)>,     eps = E_e eps_e.
```

For item 1 take an optimal solution; one exists because the feasible Gram
matrices form a compact set and the objective is linear. So `eps = 1 - sdp(U)`.
Reversing an edge `(u, v, sigma)` to `(v, u, sigma^(-1))` leaves `eps_e` and
satisfaction unchanged.

## (1) The fourth-tensor embedding

For a vertex `u` put `p_a = ||u_a||`. When `p_a > 0` put `ubar_a = u_a/p_a`;
when `p_a = 0` the label is *dead* and contributes nothing below. Define

```text
N(u) = sum_(a live) p_a ubar_a^(x4)   in H = (R^d)^(x4).
```

Since `<ubar_a^(x4), ubar_b^(x4)> = <ubar_a, ubar_b>^4 = 1[a = b]` for live
labels, `||N(u)||^2 = sum_a p_a^2 = 1`.

For two vertices `u, w` with norms `p_a, r_c` put
`S_ac = <ubar_a, wbar_c>^2` if both labels are live, and `S_ac = 0` otherwise.
Then

```text
eta(u, w) := 1 - <N(u), N(w)> = (1/2) ||N(u) - N(w)||^2 = 1 - sum_(a,c) p_a r_c S_ac^2.
```

Every row and column sum of `S` is `<= 1`, by Bessel's inequality for the
orthonormal family `(wbar_c)` (respectively `(ubar_a)`).

**Lemma 1.1** (`s^4 >= 4s - 3` on `[-1, 1]`). Let `f(s) = s^4 - 4s + 3`. Then
`f'(s) = 4(s^3 - 1) <= 0` on `[-1, 1]`, so `f(s) >= f(1) = 0`.

**Lemma 1.2** (edge lemma). For an edge `e = (u, v, sigma)` with norms `p_a` at
`u` and `q_b` at `v`,
`||N(u) - N(v)||^2 <= 8 eps_e`.

*Proof.* Put `s_a = <ubar_a, vbar_(sigma a)>` if `a` and `sigma a` are both
live, and `s_a = 0` otherwise. Then `p_a q_(sigma a) s_a = <u_a, v_(sigma a)>`,
so `sum_a p_a q_(sigma a) s_a = 1 - eps_e`. All terms of
`<N(u), N(v)> = sum_(a,b) p_a q_b <ubar_a, vbar_b>^4` are nonnegative, so keeping
`b = sigma a` and using Lemma 1.1 gives

```text
<N(u), N(v)> >= sum_a p_a q_(sigma a) s_a^4
             >= 4 sum_a p_a q_(sigma a) s_a - 3 sum_a p_a q_(sigma a)
             >= 4 (1 - eps_e) - 3 = 1 - 4 eps_e,
```

because `sum_a p_a q_(sigma a) <= 1` by Cauchy--Schwarz. Hence
`||N(u) - N(v)||^2 = 2 - 2<N(u), N(v)> <= 8 eps_e`. QED.

**Lemma 1.3** (edge norms). With the same notation,
`sum_a p_a q_(sigma a) (1 - s_a) <= eps_e` and
`sum_a (p_a - q_(sigma a))^2 <= 2 eps_e`.

*Proof.*
`eps_e = (1 - sum_a p_a q_(sigma a)) + sum_a p_a q_(sigma a)(1 - s_a)`.
Both summands are nonnegative, the first by Cauchy--Schwarz and the second
because `s_a <= 1`. Also
`sum_a (p_a - q_(sigma a))^2 = 2 - 2 sum_a p_a q_(sigma a)
<= 2 - 2 sum_a p_a q_(sigma a) s_a = 2 eps_e`,
using `s_a <= 1` and `p, q >= 0`. QED.

## (2) The matching lemma

Fix vertices `u, w` with norms `p_a, r_c`, matrix `S`, and `eta = eta(u, w)`.

**Lemma 2.1** (deficit identity).

```text
eta = (1/2) sum_a p_a^2 (1 - sum_c S_ac^2) + (1/2) sum_c r_c^2 (1 - sum_a S_ac^2)
      + (1/2) sum_(a,c) (p_a - r_c)^2 S_ac^2.
```

*Proof.* Expand the last sum as
`(1/2) sum_a p_a^2 sum_c S_ac^2 + (1/2) sum_c r_c^2 sum_a S_ac^2
- sum_(a,c) p_a r_c S_ac^2`. Adding the first two terms and using
`sum_a p_a^2 = sum_c r_c^2 = 1` gives `1 - sum p_a r_c S_ac^2 = eta`. QED.

All three terms are nonnegative, because `sum_c S_ac^2 <= (sum_c S_ac)^2 <= 1`
and likewise for columns.

**Definition.** `tau(a) = c` if `S_ac > 1/2`. Row sums are `<= 1`, so there is
at most one such `c` for each `a`. Column sums are `<= 1`, so there is at most
one such `a` for each `c`. Hence `tau = tau_(u,w)` is a partial injection. Write
`D` for its domain and `T = tau(D)` for its range. For `a` in `D` put
`S_a = S_(a, tau a)`.

**Lemma 2.2.**

1. `sum_(a not in D) p_a^2 <= 4 eta` and `sum_(c not in T) r_c^2 <= 4 eta`.
2. `sum_(a in D) p_a^2 (1 - S_a) <= 2 eta` and
   `sum_(a in D) r_(tau a)^2 (1 - S_a) <= 2 eta`.
3. `sum_(a in D) (p_a - r_(tau a))^2 <= 8 eta`.

*Proof.*
1. If `a` is not in `D`, every `S_ac <= 1/2`. So
   `sum_c S_ac^2 <= (1/2) sum_c S_ac <= 1/2`, and `1 - sum_c S_ac^2 >= 1/2`.
   The first term of Lemma 2.1 is then at least
   `(1/4) sum_(a not in D) p_a^2`. Columns are symmetric, using the second
   term.
2. For `a` in `D`,
   `sum_(c != tau a) S_ac^2 <= (sum_(c != tau a) S_ac)^2 <= (1 - S_a)^2`. So
   `1 - sum_c S_ac^2 >= 1 - S_a^2 - (1 - S_a)^2 = 2 S_a (1 - S_a) >= 1 - S_a`,
   since `S_a > 1/2`. The first term of Lemma 2.1 gives the first bound. The
   same computation on column `tau a`, with the second term, gives the second.
3. The third term of Lemma 2.1 is at least
   `(1/2) sum_(a in D) (p_a - r_(tau a))^2 S_a^2`, and `S_a^2 > 1/4`. QED.

**Lemma 2.3** (geometry). Let `x, y, z` be unit vectors with
`<x, z>^2 >= 0.9` and `<y, z>^2 >= 0.9`. Then `<x, y>^2 >= 0.64`. If moreover
`y'` is a unit vector orthogonal to `y`, then `|<x, y'>| <= 0.6`.

*Proof.* Replace `x, y` by `+-x, +-y` so that `<x, z>, <y, z> >= sqrt(0.9)`.
Write `x = alpha z + x'` and `y = beta z + y''` with `x', y''` orthogonal to `z`.
Then `alpha, beta >= sqrt(0.9)` and `||x'||, ||y''|| <= sqrt(0.1)`, so
`<x, y> = alpha beta + <x', y''> >= 0.9 - 0.1 = 0.8`. Since `y, y'` are
orthonormal, `<x, y>^2 + <x, y'>^2 <= ||x||^2 = 1`, so `<x, y'>^2 <= 0.36`.
QED.

## (3) Root rounding of one edge

**Root rounding.** Fix a root `w` with norms `r_c`. Draw `c` in `[k]` with
probability `r_c^2`. Each vertex `u` in some fixed set gets
`x_u = tau_(u,w)^(-1)(c)` if `c` is in `T_u = tau_(u,w)(D_u)`, and an arbitrary
label otherwise.

**Lemma 3.1.** Let `e = (u, v, sigma)` be an edge with both endpoints rounded
from the same root `w` and the same draw `c`. Write `eta_u = eta(u, w)` and
`eta_v = eta(v, w)`. Then

```text
Pr[e not satisfied] <= 40 eta_u + 24 eta_v + 14 eps_e,
Pr[e not satisfied] <= 32 eta_u + 32 eta_v + 14 eps_e.
```

*Proof.* Write `p, q, r` for the norms at `u, v, w`, `S^u = S^(u,w)`,
`S^v = S^(v,w)`, `tau_u, tau_v` and `T_u, T_v`. The edge is satisfied whenever
`c` is in `T_u` and in `T_v`, and `tau_v^(-1)(c) = sigma(tau_u^(-1)(c))`. So the
failure probability is at most the `r^2`-mass of the following sets of `c`:

* (o) `c` not in `T_u`, or `c` not in `T_v`. Their mass is
  `<= 4 eta_u + 4 eta_v` by Lemma 2.2.1.
* (i) `c = tau_u(a)` with `S^u_(a c) < 0.9`. Their mass is
  `sum r_c^2 <= 10 sum_(a in D_u) r_(tau_u a)^2 (1 - S^u_a) <= 20 eta_u`, by
  Lemma 2.2.2.
* (ii) `c = tau_v(b)` with `S^v_(b c) < 0.9`. Their mass is `<= 20 eta_v`, in the
  same way.
* (iii) The rest: `c = tau_u(a) = tau_v(b)` with `S^u_(ac) >= 0.9`,
  `S^v_(bc) >= 0.9` and `b != sigma a`. Let `B` be the set of such `a`.

For `a` in `B`, the labels `a` (at `u`), `c` (at `w`) and `b` (at `v`) are live,
since `S > 0`. If `sigma a` is live at `v`, then `vbar_(sigma a)` is orthogonal
to `vbar_b`. Lemma 2.3 with `x = ubar_a`, `z = wbar_c`, `y = vbar_b` and
`y' = vbar_(sigma a)` gives `s_a <= 0.6`. If `sigma a` is dead,
`p_a q_(sigma a) = 0`. In both cases `p_a q_(sigma a) <= 2.5 p_a q_(sigma a) (1 - s_a)`.
So by Lemma 1.3, `sum_(a in B) p_a q_(sigma a) <= 2.5 eps_e`.

Put `X^2 = sum_(a in B) p_a^2`. By Cauchy--Schwarz and Lemma 1.3,

```text
X^2 = sum_B p_a q_(sigma a) + sum_B p_a (p_a - q_(sigma a))
    <= 2.5 eps_e + X sqrt(2 eps_e) <= 2.5 eps_e + eps_e + X^2/2,
```

so `X^2 <= 7 eps_e`. Since `r_c^2 <= 2 p_a^2 + 2 (p_a - r_c)^2`, Lemma 2.2.3
gives mass `sum_(a in B) r_(tau_u a)^2 <= 14 eps_e + 16 eta_u` for (iii).

Adding the four parts gives the first bound. Satisfaction and `eps_e` do not
change when the edge is reversed. Applying the first bound to
`(v, u, sigma^(-1))` gives `40 eta_v + 24 eta_u + 14 eps_e`, and averaging the
two bounds gives the second. QED.

The replay script computes the exact failure probability on random feasible
configurations and finds no violation of the first bound.

## (4) Energy, projection and residual

Let `L2(pi; H)` be the space of maps `f : V -> H` with
`<f, g> = sum_u pi(u) <f(u), g(u)>`. The operator `(Af)(u) = sum_v A(u,v) f(v)`
is self-adjoint on it, because `pi(u) A(u,v) = w(u,v)/2W` is symmetric. Take a
`pi`-orthonormal eigenbasis `h_1, ..., h_N` of `A` on `L2(pi)` with
`A h_i = lambda_i h_i` and `lambda_1 >= ... >= lambda_N`. Every `f` expands
uniquely as `f = sum_i h_i c_i` with `c_i = sum_u pi(u) h_i(u) f(u)` in `H`, and
`||f||^2 = sum_i ||c_i||^2`.

**Lemma 4.1** (Dirichlet form).

```text
<f, (I - A) f> = (1/2) E_e ||f(u) - f(v)||^2 = sum_i (1 - lambda_i) ||c_i||^2.
```

*Proof.* `sum_(u,v) pi(u) A(u,v) ||f(u) - f(v)||^2` sums
`w(u,v)/2W ||f(u) - f(v)||^2` over ordered pairs. That is
`sum_e (w_e/W) ||f(u) - f(v)||^2 = E_e ||f(u) - f(v)||^2`. Expanding the square
and using that the rows of `A` sum to 1 and that `pi A` is symmetric gives
`2<f, f> - 2<f, Af>`. The spectral form follows from the expansion. QED.

Let `m` be the number of `i` with `lambda_i > 1 - gamma`. By hypothesis
`m <= r`, and `m >= 1` because `lambda_1 = 1` with `h_1 = 1`. Let `P` keep the
first `m` terms of the expansion, and put `x(u) = (PN)(u)` and
`R(u) = N(u) - x(u)`.

**Lemma 4.2.**

1. `E_e ||x(u) - x(v)|| <= sqrt(8 eps)`.
2. `E_pi ||R(u)||^2 <= 4 eps/gamma`.
3. Every `x(u)` lies in the subspace `span(c_1, ..., c_m)` of `H`, which has
   dimension at most `m`.

*Proof.*
1. By Lemma 4.1 and Lemma 1.2, `<N, (I - A)N> = (1/2) E_e ||N(u) - N(v)||^2
   <= 4 eps`. Lemma 4.1 applied to `PN` keeps only the first `m`
   nonnegative terms of the same sum, so `<PN, (I - A)PN> <= 4 eps`. Hence
   `E_e ||x(u) - x(v)||^2 <= 8 eps`, and Cauchy--Schwarz gives the bound.
2. `R = sum_(i > m) h_i c_i`, and `1 - lambda_i >= gamma` for `i > m`. So
   `E_pi ||R||^2 = sum_(i>m) ||c_i||^2 <= (1/gamma) <N, (I - A)N> <= 4 eps/gamma`.
3. `x(u) = sum_(i <= m) h_i(u) c_i`. QED.

If `m = 1`, `x(u) = c_1` is the same for every `u`.

## (5) Grid rounding and item 1

Identify `span(c_1, ..., c_m)` isometrically with `R^m'`, `m' <= m`, and fix
`Delta > 0`. Put `ell = Delta/sqrt(m')` and draw a shift `theta` uniformly from
`[0, ell)^m'`. The cells are the half-open cubes
`prod_j [theta_j + n_j ell, theta_j + (n_j + 1) ell)` with integers `n_j`. Each
cell has diameter `Delta`. If `m = 1`, use a single cell containing every vertex
(diameter 0).

**Lemma 5.1.** `Pr_theta[x(u), x(v) in different cells] <= r ||x(u) - x(v)||/Delta`.

*Proof.* Coordinate `j` separates the two points with probability
`min(1, |x_j(u) - x_j(v)|/ell)`. A union bound over coordinates and
Cauchy--Schwarz give at most `sqrt(m') ||x(u) - x(v)||/ell
= m' ||x(u) - x(v)||/Delta`, and `m' <= r`. QED.

**Algorithm (existential).** Given the shift, choose in each nonempty cell `C` a
root `w_C` in `C` minimizing `||R(w)||` over `w` in `C`. Independently for each
cell, draw `c_C` with probability `r_c(w_C)^2` and root-round every vertex of `C`
from `w_C` with draw `c_C`.

**Lemma 5.2.** For every shift, `E_pi eta(u, w_(C(u))) <= 1.5 Delta^2 + 12 eps/gamma`.

*Proof.* For `u` in `C` with root `w`,
`||N(u) - N(w)|| <= ||x(u) - x(w)|| + ||R(u)|| + ||R(w)||
<= Delta + ||R(u)|| + ||R(w)||`. So
`eta(u,w) = (1/2)||N(u) - N(w)||^2 <= 1.5 (Delta^2 + ||R(u)||^2 + ||R(w)||^2)`.
By minimality,
`sum_(u in C) pi(u) ||R(w_C)||^2 <= sum_(u in C) pi(u) ||R(u)||^2`. Summing over
cells gives `E_pi eta <= 1.5 Delta^2 + 3 E_pi ||R||^2`. Apply Lemma 4.2.2. QED.

**Proof of item 1.** Fix a shift. An edge in one cell fails with probability
`<= 32 eta_u + 32 eta_v + 14 eps_e`, by Lemma 3.1 with the root of its cell. Any
other edge counts as a failure. Since
`E_e [eta(u, w_C(u)) + eta(v, w_C(v))] = sum_u (deg(u)/W) eta(u, w_C(u))
= 2 E_pi eta(u, w_C(u))`, Lemma 5.2 gives

```text
E_(c) [1 - val] <= Pr_(e, theta)[cut] + 64 (1.5 Delta^2 + 12 eps/gamma) + 14 eps.
```

Here the separated edges are bounded by 1 and the nonnegative
`eta`-terms of all edges are included. Averaging over the shift,
Lemmas 5.1 and 4.2.1 give

```text
1 - E val <= r sqrt(8 eps)/Delta + 96 Delta^2 + 768 eps/gamma + 14 eps.
```

Some labeling attains at least the expectation, so `val(U)` is at least the
right-hand side. If `m = 1`, the single cell cuts nothing and has diameter 0,
which gives `val(U) >= 1 - 768 eps/gamma - 14 eps`. Otherwise, if `eps = 0`, let
`Delta -> 0`. If `eps > 0`, put `A0 = r sqrt(8 eps)` and choose
`Delta = (A0/192)^(1/3)`. Then `A0/Delta = 192 Delta^2`, and the two grid terms
sum to `288 (A0/192)^(2/3) = 576 r^(2/3) eps^(1/3)/192^(2/3)`, because
`A0^(2/3) = 2 r^(2/3) eps^(1/3)`. Since `192^(2/3) > 33`, this is
`< 18 r^(2/3) eps^(1/3)`. QED.

(If every `c_i` is zero, then `m' = 0` and all `x(u)` coincide; use the single
cell as for `m = 1`.)

## (6) Items 2 and 3

Write `Loss(t) = 768 t/gamma + 14 t + 18 r^(2/3) t^(1/3)`, which is increasing
in `t >= 0`.

**Proof of item 2.**

*Solver input.* Index matrices by `V x [k]`, with `n = Nk`. The SDP is the
program of `sdp-fixed-precision-solvable-gls` with:

* `C = -(1/2W) sum_e w_e sum_a (E_((u,a),(v,sigma_e a)) + E_((v,sigma_e a),(u,a)))`,
  where `E_(p,q)` is a matrix unit;
* the constraints `X_((u,a),(u,b)) = 0` for `a != b`, in symmetric form;
* the constraints `sum_a X_((u,a),(u,a)) = 1` for each `u`.

Gram matrices of feasible vector solutions are exactly the feasible `X`,
because every PSD matrix is a Gram matrix. The objective matches, so
`sdp(U) = -inf <C, X>`. The data are rational of size polynomial in the input
size `Z` of `U`, and `m <= N k^2`.

*Ball verification.* Take `X0 = I/k`, which is feasible.

* Inner ball: let `Y` be in `L` with `||Y||_F <= 1/k`. Then
  `lambda_min(X0 + Y) >= 1/k - ||Y||_op >= 1/k - ||Y||_F >= 0`, so `X0 + Y`
  is in `F`. So `r = 1/k`.
* Outer ball: let `X` be in `F`. Its diagonal entries are nonnegative and sum to
  1 over each block, so they are `<= 1`. By PSD-ness,
  `|X_pq| <= sqrt(X_pp X_qq) <= 1`, so `||X||_F <= n`. Then
  `||X - X0||_F <= n + ||X0||_F <= 2n`. So `R = 2Nk`.

`log(R/r) = log(2Nk^2)`. With precision `eps0/3`, the import returns in time
`poly(Z)` a feasible `X*` with `obj(X*) := -<C, X*>` satisfying
`sdp(U) - eps0/3 <= obj(X*) <= sdp(U)`. Accept iff `obj(X*) >= 1 - 1.5 eps0`.

*Correctness.*

* If `val(U) >= 1 - eps0`, then `sdp(U) >= 1 - eps0`. So
  `obj(X*) >= 1 - 4 eps0/3`, and the algorithm accepts.
* Suppose `val(U) <= delta` and the walk has at most `r` eigenvalues above
  `1 - gamma`. If `sdp(U) >= 1 - 2 eps0`, then item 1 and monotonicity give
  `val(U) >= 1 - Loss(2 eps0) > delta`, by the hypothesis of item 2, a
  contradiction. So `obj(X*) <= sdp(U) < 1 - 2 eps0`, and the algorithm
  rejects.

The algorithm never uses `r` or `gamma`, and its running time is polynomial in
`Z` for every `k`. QED.

**Proof of item 3.** Compose `Red` with the algorithm of item 2. On a
satisfiable formula the output has value `>= 1 - eps0` and is accepted. On an
unsatisfiable formula it has value `<= delta` and at most `r(Z)` eigenvalues
above `1 - gamma`, and it is rejected. So 3SAT is in P.

Item 2 holds for each output separately, so `r` and `gamma` may depend on `Z`
as long as the inequality holds for each output. The hypothesis of item 2 needs
only that inequality at the given `r, gamma`.

*Sufficient condition.* If `r < (1 - delta)^(3/2)/(216 sqrt(2 eps0))`, then
`r^(2/3) < (1 - delta)/(36 (2 eps0)^(1/3))`, using `216^(2/3) = 36`. So
`18 r^(2/3) (2 eps0)^(1/3) < (1 - delta)/2`. If
`gamma >= 3072 eps0/(1 - delta - 56 eps0)` with `56 eps0 < 1 - delta`, then
`1536 eps0/gamma <= (1 - delta - 56 eps0)/2`, so
`1536 eps0/gamma + 28 eps0 <= (1 - delta)/2`. Adding the two gives the item 2
inequality. QED.

## Where each member of the class fails

A reduction `Red` in the class maps unsatisfiable formulas to games whose walks
have at most `r` eigenvalues above `1 - gamma`, with `(r, gamma)` in the region
of item 2. Its soundness analysis must certify `val <= delta`, but Section 5
turns any SDP solution of value `>= 1 - 2 eps0` on such an output into a
labeling of value `> delta`. So the soundness case forces `sdp <= 1 - 2 eps0` on
every NO output, while completeness forces `sdp >= 1 - eps0` on every YES
output. The degree-2 SDP then separates them. A reduction escapes only by
putting at least `(1 - delta)^(3/2)/(216 sqrt(2 eps0))` eigenvalues above
`1 - 3072 eps0/(1 - delta - 56 eps0)` into some NO outputs. Unless `P = NP`,
it must do so on infinitely many NO outputs: finitely many exceptions can be
hard-wired into the algorithm.
