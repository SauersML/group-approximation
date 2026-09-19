---
rg: 2
id: brin-thompson-nv-sum-type-size-functions-are-not-cnd-proof
kind: route
title: "Subadditivity of the square root of a cnd function caps it at the square of the word length, while an explicit length-(3d+1) word holds 2^d disjoint baker pieces; plus integer l^p certificates on Z^3 for p > 2"
target: brin-thompson-nv-sum-type-size-functions-are-not-cnd
requires:
  - brin-thompson-2v-brick-count-is-exponentially-distorted
artifacts:
  - experiments/brin-thompson-cnd-2026-09-18/brick_compression.py
  - experiments/brin-thompson-cnd-2026-09-18/lp_certificates.py
  - experiments/brin-thompson-cnd-2026-09-18/lp_certificates.json
---

Notation is as in the target.

**Step 0 (the cnd length function).** Let `Psi: nV -> R` be cnd. Then `Psi - Psi(e)` is cnd
(adding a constant does not change the quadratic form on zero-sum vectors), it vanishes at `e`, and
it is symmetric. By Schoenberg's theorem in its group form (Bekka--de la Harpe--Valette,
*Kazhdan's Property (T)*, Proposition C.2.2 and Corollary C.2.4), there are a unitary representation
`pi` of `nV` on a Hilbert space `H` and a 1-cocycle `b: nV -> H` with

  `Psi(g) - Psi(e) = ||b(g)||^2`,   `b(gh) = b(g) + pi(g) b(h)`.

Hence `q(g) := sqrt(Psi(g) - Psi(e))` is a length function: `q(e) = 0`, `q(g^{-1}) = q(g)` (because
`b(g^{-1}) = -pi(g)^{-1} b(g)`), and `q(gh) <= q(g) + q(h)`. Consequently, for a word
`g = s_1 ... s_l` in a set `T` of elements closed under inverses,

  `Psi(g) <= Psi(e) + l^2 max_{s in T} (Psi(s) - Psi(e))`.                              (*)

**Step 1 (item 1).** By item 2 of `brin-thompson-2v-brick-count-is-exponentially-distorted`,
`B_d = (beta^{-1} tau)^d beta^{d+1}`, a word of length `3d + 1` in `T = {beta^{+-1}, tau}`. Apply
(*) with `K_0 = max(Psi(beta), Psi(tau)) - Psi(e)` (using `Psi(beta^{-1}) = Psi(beta)`):

  `Psi(B_d) <= Psi(e) + (3d+1)^2 K_0`.

By item 5 of the same claim, `T_d = beta^{-d} (sigma x id) beta^{d}` is a word of length `2d + 1` in
`{beta^{+-1}, sigma x id}`, so `Psi(T_d) <= Psi(e) + (2d+1)^2 K_1` with
`K_1 = max(Psi(beta), Psi(sigma x id)) - Psi(e)`. This is item 1.

**Step 2 (item 2).** Take `S = {w : |w| = d}`, an antichain, and `k_w = 1` for all `w`. By item 1
of `brin-thompson-2v-brick-count-is-exponentially-distorted`, `g(S,k) = B_d`, and

  `A_p(S,k) = (sum_{|w| = d} 1)^{1/p} = 2^{d/p}`.

Let `F` be nondecreasing with `Psi(g(S,k)) >= F(A_p(S,k))` for all antichains and exponents. Given
`t >= 1`, put `d = ceil(p log_2 t)`, so that `A_p = 2^{d/p} >= t` and `d <= p log_2 t + 1`. Then

  `F(t) <= F(2^{d/p}) <= Psi(B_d) <= Psi(e) + (3d+1)^2 K_0 <= Psi(e) + (3 p log_2 t + 4)^2 K_0`,

which is `O_p((log t)^2)`. This is the displayed inequality of item 2 (for `t = 2^{d/p}` the cruder
constant `(3 p log_2 t + 1)^2` holds, since then `d = p log_2 t` exactly).

*The asymptotic form.* Suppose instead `psi` is cnd, `M in R`, `Psi = psi + M(1 - delta_e)` is cnd,
`G` is regularly varying of index `gamma > 0` at infinity, and
`Psi(g(S,k)) / G(A_p(S,k)) -> kappa > 0` as `A_p(S,k) -> infinity`. Regular variation of positive
index gives, by the Potter bounds (Bingham--Goldie--Teugels, *Regular Variation*, Theorem 1.5.6),
a `t_0` with `G(t) >= t^{gamma/2}` for `t >= t_0`. Along `B_d` this yields

  `Psi(B_d) >= (kappa/2) G(2^{d/p}) >= (kappa/2) 2^{d gamma / (2p)}`

for all large `d`, against `Psi(B_d) <= Psi(e) + (3d+1)^2 K_0`. The two are incompatible for large
`d`, so no such `Psi` is cnd. Note that `M` and `psi(e)` enter only through the constant `Psi(e)`,
so adding `M(1 - delta_e)` cannot rescue a candidate, exactly as in
`brin-thompson-nv-max-type-size-functions-are-not-cnd`.

**Step 3 (item 3: the `l^p` certificates on the fixed `Z^3`).** For the antichain
`S = {00, 01, 1}` and `k = (m, q, r)`, `g(S,k)` is the element `g(w)` of
`brin-thompson-nv-max-type-size-functions-are-not-cnd` and `A_p(S,k) = ||(m,q,r)||_p`. The map
`Z^3 -> nV`, `(m,q,r) |-> g(S,k)`, is an injective homomorphism (disjoint supports), so the
restriction of a cnd function of `nV` to its image is a cnd function of `Z^3`.

*The scaling limit.* Suppose `Psi` is cnd on `nV` and `Psi(g(S,k)) / G(||k||_p) -> kappa > 0` as
`||k||_p -> infinity`, with `G` regularly varying of index `gamma > 0`, the convergence
`G(lambda r)/G(lambda) -> r^gamma` being uniform on compact subsets of `(0, infinity)`. Let
`c in Z^{S_k}` be a zero-sum vector on a finite grid `S_k subset Z^3` with
`Q = sum_{x,y} c_x c_y ||x - y||_p^gamma > 0`. For `lambda in N` put `h_x = g(S, lambda x)`, so that
`h_x^{-1} h_y = g(S, lambda(y - x))`. Then, exactly as in Step 5 of
`brin-thompson-nv-max-type-size-functions-are-not-cnd-proof` (there written for the `l^inf` norm;
only the norm changes),

  `Psi(h_x^{-1} h_y) / G(lambda) = [Psi(g(S, lambda(y-x))) / G(lambda ||y - x||_p)]
                                   . [G(lambda ||y - x||_p) / G(lambda)] -> kappa ||y - x||_p^gamma`

for `x != y`, while the diagonal contributes the constant `Psi(e) sum_x c_x^2` and `G(lambda) ->
infinity` (Step 5.1 there). Hence
`sum_{x,y} c_x c_y Psi(h_x^{-1} h_y) / G(lambda) -> kappa Q > 0`, so the form is positive for large
`lambda` and `Psi` is not cnd. Adding `M(1 - delta_e)` only changes the constant term, as there.
So a certificate for `||x - y||_p^gamma` kills every such `Psi`.

*Certificates.* `lp_certificates.py` produces, for each `p` in
`{2.15, 2.25, 2.5, 3, 4, 6, 10}`, an integer vector `c` on a grid `S_k = {-k..k}^3` with
`sum_x c_x = 0`. Pairs are classified by the sorted triple `t = (a <= b <= c)` of absolute
coordinate differences; the class counts `N_t = sum_{pairs in class t} c_x c_y` are exact integers,
and

  `Q_p = sum_t N_t (a^p + b^p + c^p)^{1/p}`

is evaluated in 80-digit `Decimal` arithmetic, whose truncation error is bounded by
`10^{-70} sum_t |N_t| d_t`, many orders below `Q_p`. The stored values (grid half-width `k`, and
`Q_p`) are

  `p = 2.15, k = 5, Q_p = 3.84e10`;  `p = 2.25, k = 4, Q_p = 2.12e11`;
  `p = 2.5,  k = 2, Q_p = 8.66e10`;  `p = 3,    k = 2, Q_p = 7.05e11`;
  `p = 4,    k = 2, Q_p = 2.73e12`;  `p = 6,    k = 2, Q_p = 5.09e12`;
  `p = 10,   k = 2, Q_p = 6.53e12`.

`python3 lp_certificates.py --verify` recomputes all of them from the stored integer vectors with
integers and `Decimal` only. So `||x - y||_p` is not cnd on `Z^3` for these `p`. By Step 4 of
`brin-thompson-nv-max-type-size-functions-are-not-cnd-proof` (if `K >= 0` with zero diagonal is cnd
on a finite set then so is `K^alpha` for `0 < alpha < 1`), `||x - y||_p^{gamma}` is not cnd for any
`gamma >= 1` either: were it cnd, its `(1/gamma)`-th power `||x - y||_p` would be cnd.

*Sharpness at `p = 2`.* For `1 <= p <= 2` no certificate exists. Let `theta_1, theta_2, theta_3` be
i.i.d. symmetric `p`-stable random variables, `E e^{i s theta} = e^{-|s|^p}` (Gaussian for `p = 2`).
Then `E|sum_i a_i theta_i| = c_p ||a||_p` with `c_p = E|theta_1| in (0, infinity)`, because
`sum_i a_i theta_i` has the law of `||a||_p theta_1`. So `a |-> sum_i a_i theta_i` is an isometry of
`l_p^3` onto a subspace of `L^1`, up to the factor `c_p`. And every `L^1` metric is of negative
type: for `s in R` set `Phi(s) = 1_{(-infinity, s]} - 1_{(-infinity, 0]} in L^2(R)`, so that
`Phi(s) - Phi(t) = +-1_{(t, s]}` and `||Phi(s) - Phi(t)||^2_{L^2(R)} = |s - t|`; then for
`f, g in L^1(Omega)`,
`||f - g||_1 = int_Omega ||Phi(f(omega)) - Phi(g(omega))||^2_{L^2(R)} d omega
             = ||Phi o f - Phi o g||^2_{L^2(Omega x R)}`,
a squared Hilbert-space distance, hence a kernel of negative type. Therefore `||x - y||_p` is cnd
on `R^3` for `1 <= p <= 2`, and `p <= 2` survives item 3 for a reason, not for lack of search.
(For `p > 2` the general statement that `l_p^3` does not embed in `L^1` is Dor's theorem; it is
**not** imported here, and item 3 claims only the certified list.)

**Step 4 (item 4).** Let `Psi` be cnd on `nV` and `F` nondecreasing with
`Psi(k) >= F(#\{level-m cubes moved by k\})` for `k in K_m`. By item 5 of
`brin-thompson-2v-brick-count-is-exponentially-distorted`, `T_d in K_{d+1}` moves all
`N = 2^{n(d+1)}` cubes of level `d+1`, so `d + 1 = (log_2 N)/n`, and by Step 1

  `F(N) <= Psi(T_d) <= Psi(e) + (2d+1)^2 K_1 = Psi(e) + ((2 log_2 N)/n - 1)^2 K_1`,

which is `O((log N)^2)`.

**Step 5 (item 5).** For `p = infinity`, `A_infinity` restricted to the antichain `{00, 01, 1}` is
the `l^inf` norm on `Z^3`, and `brin-thompson-nv-max-type-size-functions-are-not-cnd` (item 2)
kills every `Psi` asymptotic to `G(A_infinity)` for `G` regularly varying of index `>= 1/4`. For
`1 <= p < infinity`, Step 2 kills every `Psi` asymptotic to `G(A_p)` for `G` regularly varying of
any positive index. Together these exhaust `p in [1, infinity]`.

**Step 6 (verification).** `brick_compression.py` re-derives every group-theoretic input of Steps 1
and 4 with exact brick arithmetic for `0 <= d <= 8`: the closed forms `B_d = (beta^{-1}tau)^d
beta^{d+1}` and `T_d = beta^{-d} T_0 beta^d`, the identification of `B_d` with the product of the
`2^d` pairwise disjoint-support commuting baker maps, `L(B_d) = 2^{d+1}` by the exact guillotine DP,
the constant exponent cocycle of `B_d`, and `c(T_d) = 0`.
