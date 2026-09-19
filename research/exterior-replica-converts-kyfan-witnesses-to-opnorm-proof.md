---
rg: 2
id: exterior-replica-converts-kyfan-witnesses-to-opnorm-proof
kind: route
title: Read Ky Fan sums as operator-norm angles of exterior powers below the wrap threshold, drop to the largest index below it, and extract a Ky Fan index from any gauge by Abel summation of its dual vector
target: exterior-replica-converts-kyfan-witnesses-to-opnorm
requires:
  - classical-unitary-ratio-witnesses-amplify-to-metric-models
  - thompson-v-finitely-presented-infinite-simple
artifacts:
  - experiments/exterior-replica-kyfan-2026-09-17/check_exterior_replica.py
  - experiments/exterior-replica-kyfan-2026-09-17/output.txt
---

Notation is that of the claim. For `g in U(d)` write its eigenvalues as `lambda_i = e^(i theta_i)` with principal angles
`theta_i in (-pi, pi]`, so that `s_i = |lambda_i - 1| = 2 sin(|theta_i| / 2)`. Since `2 sin(x/2)` is increasing on `[0, pi]`
and `(2/pi) x <= 2 sin(x/2) <= x` there,

```text
(2/pi) |theta_i| <= s_i <= |theta_i|,                                               (E)
```

and the `k` indices with the largest `s_i` are also `k` indices with the largest `|theta_i|`.

## 0. Exterior powers

For `1 <= j <= d`, `Lambda^j g` acts on `Lambda^j C^d` by `v_1 ^ ... ^ v_j -> g v_1 ^ ... ^ g v_j`.

- `Lambda^j(gh) = Lambda^j(g) Lambda^j(h)` and `Lambda^j(g^*) = Lambda^j(g)^*`, so `Lambda^j` maps `U(d)` into `U(binom(d, j))`
  as a continuous homomorphism. Its matrix in the basis `e_S = e_(s_1) ^ ... ^ e_(s_j)` is the `j`-th compound matrix, whose
  entries are the `j x j` minors of `g`; multiplicativity is the Cauchy--Binet formula.
- If `g` is diagonal in an orthonormal eigenbasis `(v_i)`, then `v_S = v_(s_1) ^ ... ^ v_(s_j)` over `j`-subsets `S`
  form an orthonormal eigenbasis of `Lambda^j g`, with eigenvalue `lambda_S = prod_(i in S) lambda_i`.

So `Phi_k = (+)_(j <= k) Lambda^j` is a continuous homomorphism `U(d) -> U(D)`, and its eigenvalues are the `lambda_S` over
all nonempty `S` with `|S| <= k`. Since `Phi_k(g)` is unitary, hence normal,

```text
l_op(Phi_k(g)) = max_(1 <= |S| <= k) |lambda_S - 1|.                                  (O)
```

Applying `Phi_k` coordinatewise to a tuple `U` gives `w(Phi_k(U)) = Phi_k(w(U))` for every word `w`, because `Phi_k` is a
homomorphism.

## 1. Exterior comparison

**Upper bound.** For unit complex numbers `x, y`, `|xy - 1| <= |x(y - 1)| + |x - 1| = |y - 1| + |x - 1|`. By induction,
`|lambda_S - 1| <= sum_(i in S) s_i`. For `|S| <= k` this sum is at most `KF_k(g)`, and (O) gives
`l_op(Phi_k(g)) <= KF_k(g)`.

**Lower bound.** Assume `KF_k(g) <= 2`, and let `T` be a set of `k` indices carrying the `k` largest `s_i`, chosen as
in (E) so that it also carries the `k` largest `|theta_i|`.

- By (E), `sum_(i in T) |theta_i| <= (pi/2) KF_k(g) <= pi`, and `sum_(i in T) |theta_i| >= KF_k(g)`.
- Split `T` into `P = {i in T : theta_i > 0}` and `N = {i in T : theta_i < 0}`. One of the two sums
  `sum_P theta_i` and `sum_N |theta_i|` is at least `KF_k(g)/2`. Replacing `g` by `conj(g)` if necessary, which does not
  change `s(g)` or `l_op(Phi_k(g))`, suppose it is `sigma = sum_P theta_i`.
- If `KF_k(g) = 0` there is nothing to prove. Otherwise `P` is nonempty, `|P| <= k` and
  `KF_k(g)/2 <= sigma <= pi`.
- `lambda_P = e^(i sigma)`, so `|lambda_P - 1| = 2 sin(sigma/2) >= (2/pi) sigma >= KF_k(g)/pi`. Now use (O).

`conj` here is entrywise conjugation, a continuous automorphism of `U(d)`; `Phi_k(conj g) = conj(Phi_k(g))` has the same
operator-norm length.

## 2. Reduction to the operator norm

Let `A = KF_k(a(U)) > 0`, since `a(U) != I`, and `rho = max_(r in R_0) KF_k(r(U))`.

- **Case `A <= 2`.** Take `j = k`. By Step 1, `l_op(a(W)) >= A/pi > 0` and `l_op(r(W)) <= KF_k(r(U)) <= rho`. So the
  ratio is at most `pi rho / A`.
- **Case `A > 2`.** Take `j = max { i <= k : KF_i(a(U)) <= 2 }`. It exists because `KF_1 <= 2`, and `j < k`.
  - The averages `KF_i / i` are nonincreasing in `i`, since the average of the top `i` entries is at least the average of the
    top `i + 1`. So `KF_j(a(U)) >= (j/(j+1)) KF_(j+1)(a(U)) > 2j/(j+1) >= 1`.
  - By Step 1, `l_op(a(W)) >= 1/pi`, and `l_op(r(W)) <= KF_j(r(U)) <= KF_k(r(U)) <= rho`. So the ratio is at most `pi rho`.

In both cases the ratio is at most `pi rho / min(A, 1)`. When `A` lies in `(1, 2]` this uses `pi rho / A <= pi rho`.

## 3. Gauge reduction

Let `N` be a symmetric gauge on `R^d` and `N^*(y) = max { <x, y> : N(x) <= 1 }` its dual norm, again a symmetric gauge.

- Finite-dimensional duality gives `N(x) = max { <x, y> : N^*(y) <= 1 }`.
- For `x >= 0` decreasing, the maximum can be taken at `y >= 0` decreasing. Replacing `y` by its decreasing rearrangement
  of absolute values keeps `N^*(y)` and, by the rearrangement inequality, does not decrease `<x, y>`.

Fix such an optimal `y` for `x = s(a(U))`, and put `c_i = y_i - y_(i+1) >= 0` with `y_(d+1) = 0`. Abel summation gives,
for every decreasing `z >= 0`,

```text
<z, y> = sum_(i=1..d) c_i KF_i(z).
```

Here `KF_i(z) = z_1 + ... + z_i`, which agrees with the matrix `KF_i` when `z = s(g)`.

- For `a`: `N(s(a(U))) = sum_i c_i KF_i(a(U))`.
- For each `r in R_0`, since `N^*(y) <= 1`: `sum_i c_i KF_i(r(U)) = <s(r(U)), y> <= N(s(r(U))) <= epsilon N(s(a(U)))`.

Sum over `r in R_0`. With `M_i = sum_(r in R_0) KF_i(r(U))`,

```text
sum_i c_i M_i  <=  |R_0| epsilon  sum_i c_i KF_i(a(U)).
```

The right side is positive, so some `i` with `c_i > 0` has `M_i <= |R_0| epsilon KF_i(a(U))`. Then
`KF_i(r(U)) <= M_i <= |R_0| epsilon KF_i(a(U))` for every `r`.

## 4. Thompson's group V

Let `a` represent a nontrivial element of `V = <S | R>`.

- **(i) => (ii).** Given `R_0` and `epsilon`, apply (i) with `epsilon / pi` and then Step 2. This gives `W` with `a(W) != I`
  and `l_op(r(W)) <= epsilon l_op(a(W))` for `r in R_0`, which is the witness condition (W) of
  `classical-unitary-ratio-witnesses-amplify-to-metric-models` for `l_op`.
- **(ii) => (i).** Take `k = 1`, so `KF_1 = l_op`. Given `R_0` and `epsilon`, an `l_op`-ratio witness for `epsilon/2` has
  `rho <= (epsilon/2) A`, and `A <= 2` gives `min(A, 1) >= A/2`. So the mass-ratio is at most `epsilon`.
- **(ii) <=> (iii).** This is part (C) of `classical-unitary-ratio-witnesses-amplify-to-metric-models`, for the simple group
  `V` (`thompson-v-finitely-presented-infinite-simple`).
- **The trace-norm corollary.** Suppose `N(s(r(U))) <= epsilon N(s(a(U)))` and `||r(U) - I||_(S_1) <= epsilon` for
  `r in R_0`.
  - Step 3 gives an index `k` with `KF_k(r(U)) <= |R_0| epsilon A`.
  - Also `KF_k(r(U)) <= ||r(U) - I||_(S_1) <= epsilon`.
  - If `A >= 1` the second bound is `epsilon min(A, 1)`. If `A < 1` the first is `|R_0| epsilon min(A, 1)`.
  - So the mass-ratio is at most `max(|R_0|, 1) epsilon`. Since `epsilon` is arbitrary for each fixed `R_0`, (i) holds.

## 5. The worked data

For eigenvalue data the quantities in Steps 1 and 2 depend only on the angle lists. The script checks the following:

- compound matrices are multiplicative and unitary to `1e-14`;
- both inequalities of Step 1 on 300 random and near-identity unitaries in `U(5)`, for all `k`;
- Step 2's bound, which is attained within a factor `0.41`;
- Step 3's index extraction for Schatten `1, 1.5, 3` and random weighted Ky Fan gauges;
- the worked data at `k = 10, 20, 40`, using (O) evaluated from angle lists.

It is a sanity check only; the proof above does not rely on it.
