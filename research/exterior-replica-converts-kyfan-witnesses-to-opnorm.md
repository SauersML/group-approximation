---
rg: 2
id: exterior-replica-converts-kyfan-witnesses-to-opnorm
kind: claim
title: Ratio witnesses in any unitarily invariant norm reduce to Ky Fan witnesses, and the exterior replica turns those with vanishing relator Ky Fan mass into operator-norm witnesses, so for Thompson's V they are exactly MF
distinct_from:
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that amplifies witnesses already given in the operator, Hilbert--Schmidt or rank length by tensor powers; this converts witnesses in an arbitrary, possibly dimension-dependent unitarily invariant norm into operator-norm witnesses by a sum of exterior powers, which no tensor power does, and then feeds them to that claim.
  schatten-p-ratio-data-defeat-tensor-replica-amplification: that shows tensor replicas cannot amplify normalized Schatten-p data; this uses the Schur-functor replica that claim left open, proves it succeeds exactly when the relator Ky Fan mass vanishes, and all of that claim's data have relator mass bounded below.
  thompson-v-has-unbounded-compact-unitary-relator-width: that is the open width statement; this is a method-level reduction and class kill for the unitarily-invariant-norm witness format of it, and decides nothing about V.
  adaptive-tensor-amplification: that converts operator separation into 2-norm separation; this converts Ky Fan ratio data into operator ratio data.
artifacts:
  - experiments/exterior-replica-kyfan-2026-09-17/check_exterior_replica.py
  - experiments/exterior-replica-kyfan-2026-09-17/output.txt
---

**ESTABLISHED** by `exterior-replica-converts-kyfan-witnesses-to-opnorm-proof`.

## Notation

For `g in U(d)` let `s(g) = (s_1 >= ... >= s_d)` be the singular values of `g - I`, that is, the numbers `|lambda_i - 1|`
over the eigenvalues `lambda_i` of `g`, in decreasing order. Put

```text
KF_k(g) = s_1 + ... + s_k          (Ky Fan k-norm of g - I, 1 <= k <= d),
l_op(g) = KF_1(g) = ||g - I||_op.
```

A **spectral gauge length** on `U(d)` is `l_N(g) = N(s(g))` for a symmetric gauge `N` on `R^d`, that is, a norm invariant
under coordinate permutations and sign changes. Every Schatten norm, normalized or not, every Ky Fan norm and every Orlicz or
weighted norm of `g - I` is of this form, and by von Neumann's theorem these are exactly the unitarily invariant norms of
`g - I`. The gauge may depend on `d` and on the witness. None of the statements below uses subadditivity of `l_N`.

The **exterior replica** of order `k <= d` is

```text
Phi_k = Lambda^1 (+) Lambda^2 (+) ... (+) Lambda^k : U(d) -> U(D),     D = sum_(j <= k) binom(d, j).
```

It is a continuous homomorphism, applied coordinatewise to tuples, so `w(Phi_k(U)) = Phi_k(w(U))` for every word `w`.

## Statement

Let `Gamma = <S | R>` be a countable presented group, `a in F(S)`, `R_0 <= R` finite, and `U in U(d)^S` with `a(U) != I`.

- **(1) Exterior comparison.** For every `g in U(d)` and `k <= d`,

  ```text
  l_op(Phi_k(g)) <= KF_k(g),      and      l_op(Phi_k(g)) >= KF_k(g) / pi   whenever KF_k(g) <= 2.
  ```

- **(2) Reduction to the operator norm.** Put `A = KF_k(a(U))` and `rho = max_(r in R_0) KF_k(r(U))`. Then for some
  `j <= k` the tuple `W = Phi_j(U)` satisfies

  ```text
  l_op(r(W)) <= (pi rho / min(A, 1)) * l_op(a(W))       for every r in R_0,      and a(W) != I.
  ```

- **(3) Gauge reduction.** If `N(s(r(U))) <= epsilon N(s(a(U)))` for every `r in R_0` and a symmetric gauge `N`, then some
  `k <= d` has `KF_k(r(U)) <= |R_0| epsilon KF_k(a(U))` for every `r in R_0`.

Call `rho / min(A, 1)` the **mass-ratio** of `(U, k)`. It is at most `max(rho/A, rho)`, so it is small as soon as both the
Ky Fan ratio and the absolute **relator Ky Fan mass** `rho` are small.

- **(4) Thompson's group V.** Let `a` represent a nontrivial element of `V`. The following are equivalent.
  - (i) For every finite `R_0 <= R` and `epsilon > 0` there are `d`, `U in U(d)^S` and `k` with `a(U) != I` and mass-ratio
    at most `epsilon`.
  - (ii) `a` has an `l_op`-ratio witness.
  - (iii) `V` is MF, in the unitary-sequence corona sense of `countable-group-mf-conventions`.

  In particular, if `a` has ratio witnesses in spectral gauge lengths (any gauges) whose relators also satisfy
  `||r(U) - I||_(S_1) -> 0` in the **unnormalized** trace norm, then `V` is MF.

## Worked data

Eigenvalue data only; realizability by words of `V` is not claimed. Let `a(U)` have `k` eigen-angles `1/k` and relators
have one eigen-angle `k^(-1/2)` and `k^3` eigen-angles `k^(-2)` (rest `1`). At the identity replica the op, HS and rank
ratios relator/`a` are about `k^(1/2)`, `sqrt 2` and `k^2`, so no classical length sees a witness. The Ky Fan-`k` ratio is
about `k^(-1/2)` and the relator mass is about `k^(-1/2)`, so (2) gives an op ratio at most about `pi k^(-1/2)`.
`output.txt` records `k = 10, 20, 40`: op ratio after `Phi_k` equal to `0.42, 0.28, 0.19`.

## What this kills

Attempt 5 on `thompson-v-has-unbounded-compact-unitary-relator-width` left open Schur-functor replicas and model-dependent
lengths among the escapes. This claim settles the norm-type part of both.

- **The class.** Ratio witnesses for `V` in any unitarily invariant norm of `g - I`, including dimension-dependent,
  witness-dependent Ky Fan, Schatten and Orlicz norms.
- **The invariant.** The relator Ky Fan mass `rho = max_r KF_k(r(U))` at the index `k` selected by (3).
- **Where every member with vanishing mass dies.** At the exterior replica, step (2). One application of `Phi_j` turns the
  witness into an operator-norm ratio witness. `classical-unitary-ratio-witnesses-amplify-to-metric-models` then amplifies it
  to an MF model. So such a witness for `V` is exactly as hard as `V` being MF.
- **What survives.** Witnesses whose relator Ky Fan mass stays bounded below at every usable index. Since the ratio tends to
  `0`, these force `KF_k(a(U)) -> infinity` and hence `k -> infinity`: `a(U)` must move unboundedly many eigenvalues by a
  total angle far beyond `pi`.
  - Normalized constant-separation models (Hilbert--Schmidt, Schatten-`p`) typically survive. A normalized defect `epsilon`
    in dimension `d` allows an absolute trace-norm defect up to `epsilon d`, so their relator mass need not vanish, and (2)
    applies to them only when it does.
  - Every finite-dimensional realization of the data of `schatten-p-ratio-data-defeat-tensor-replica-amplification`
    survives. Its relators have an eigenvalue `-1`, so `KF_k(r) >= 2` at every index. The exterior method dies there too,
    since a relator eigenvalue `-1` already gives `l_op(Phi_j r) = 2`.
- **Beyond norms.** Normalized rank and other non-norm lengths are not covered. The rank case is already handled by the
  classical amplification claim.
