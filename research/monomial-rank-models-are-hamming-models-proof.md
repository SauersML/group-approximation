---
rg: 2
id: monomial-rank-models-are-hamming-models-proof
kind: route
title: Cycle blocks of a monomial matrix minus the identity have rank at least half their length
target: monomial-rank-models-are-hamming-models
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md
---

Section 6 of the artifact.

1. **Reduction to the identity.** Rank distance and Hamming distance are both left
   invariant, and `j` is a homomorphism, so it suffices to compare `C = B^(-1) A` with `1`.
2. **Hamming side.** Write `C e_i = c_i e_(pi(i))`, and let `m` count the `i` with
   `C e_i != e_i`. The point `(lambda, i)` is moved by `j(C)` exactly when `pi(i) != i` or
   `c_i != 1`, independently of `lambda`. So `d_H(j(C), 1) = m / N`.
3. **Upper bound.** `C - 1` has at most `m` nonzero columns, so `rk(C - 1) <= m`.
4. **Lower bound.** After a simultaneous permutation of rows and columns, `C - 1` is block
   diagonal along the cycles of `pi`. A fixed point with `c_i != 1` gives the block
   `c_i - 1 != 0`, of rank `1`. A cycle `i_1 -> i_2 -> ... -> i_l` with `l >= 2` gives a
   block whose columns `c_(i_r) e_(i_(r+1)) - e_(i_r)`, for `r = 1, ..., l - 1`, restricted
   to the rows `i_1, ..., i_(l-1)`, form a lower bidiagonal matrix with `-1` on the
   diagonal. So the block has rank at least `l - 1 >= l / 2`. Summing over blocks,
   `rk(C - 1) >= m / 2`.
5. **Sofic approximation.** Replace each `sigma_k(g)` by a monomial matrix within
   `o(N_k)` rank; defects and separation change by `o(1)`. By steps 2-4,
   `d_H(j(sigma_k(g)) j(sigma_k(h)), j(sigma_k(gh))) <= 2 rk(sigma_k(g) sigma_k(h) - sigma_k(gh)) / N_k -> 0`,
   and `d_H(j(sigma_k(g)), 1) >= rk(sigma_k(g) - 1) / N_k`, which stays bounded away from
   `0` for `g != 1`. So `j o sigma_k` is a sofic approximation on the sets `X_(N_k)`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 14 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
