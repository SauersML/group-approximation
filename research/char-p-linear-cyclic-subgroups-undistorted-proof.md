---
rg: 2
id: char-p-linear-cyclic-subgroups-undistorted-proof
kind: route
title: An infinite-order element in characteristic p has an eigenvalue of absolute value above one for some absolute value, which bounds word length from below
target: char-p-linear-groups-have-no-distorted-cyclic-subgroups
requires: []
---

Let `S` be a finite symmetric generating set of `Γ`. Let `k <= K` be the field
generated over `F_p` by the entries of the elements of `S`, and let `L` be a
splitting field over `k` of the characteristic polynomial of `g`. The
eigenvalues `lambda_1, ..., lambda_n` of `g` lie in `L^x`.

**Case B: every `lambda_i` is algebraic over `F_p`.** Then each `lambda_i` lies
in a finite field, so `lambda_i^m = 1` for some `m >= 1`.
- Take the multiplicative Jordan decomposition `g = su` over an algebraic
  closure: `s` semisimple, `u` unipotent, `su = us`.
- `s` is diagonalizable with eigenvalues `lambda_i`, so `s^m = 1`.
- `(u - 1)^n = 0`, and in characteristic `p` we have `u^(p^r) - 1 = (u - 1)^(p^r)`,
  so `u^(p^r) = 1` once `p^r >= n`.
- Hence `g^(m p^r) = 1`, contradicting infinite order. So Case B is impossible.

**Case A: some `lambda = lambda_i` is transcendental over `F_p`.**
1. **An absolute value.** On `F_p(lambda)` the `lambda`-adic absolute value
   has `|lambda| = 1/2`. Absolute values extend to every extension field: to a
   purely transcendental one by the Gauss norm, then to an algebraic one. `L`
   is finitely generated over `F_p(lambda)`, so `|.|` extends to `L`. In
   characteristic `p` every absolute value is non-archimedean.
2. **Orientation.** Since `|lambda| != 1`, either `|lambda| > 1`, or `|lambda^-1| > 1`,
   and `lambda^-1` is an eigenvalue of `g^-1`. Also `|g^-k|_S = |g^k|_S`, so we may
   assume `|lambda| > 1`.
3. **A norm.** On `L^n` use the sup norm, and for `A in M_n(L)` put
   `||A|| = max_ij |a_ij|`. The ultrametric inequality gives
   `||Av|| <= ||A|| ||v||` and `||AB|| <= ||A|| ||B||`.
4. **Eigenvalue bound.** If `Av = mu v` with `v != 0` then
   `|mu| ||v|| = ||Av|| <= ||A|| ||v||`, so `|mu| <= ||A||`. Apply this to
   `A = g^k`, whose eigenvalue is `lambda^k`: `|lambda|^k <= ||g^k||`.
5. **Word length.** Put `M = max_(s in S) ||s||`. If `g^k` is a product of
   `l = |g^k|_S` generators then `||g^k|| <= M^l`, so `|lambda|^k <= M^l`. If
   `M <= 1` this contradicts `|lambda| > 1` at `k = 1`, so `M > 1` and

   `|g^k|_S >= k log|lambda| / log M`   for all `k >= 0`,

   and by step 2 the same for negative `k`.

So `c = log|lambda| / log M` works. `∎`

**Remark.** In characteristic zero the same argument, with archimedean
absolute values allowed, shows that a distorted element of a finitely generated
linear group has all eigenvalues algebraic of absolute value 1 at every place,
hence roots of unity (Kronecker), so it is virtually unipotent. That is the
known picture, and it is why O4 lives on unipotents.
