---
rg: 2
id: sl-n-q-lies-in-one-factor-of-every-normal-series-proof
kind: route
title: Direct proof with the root groups X_ij, which generate SL_n(Q)
target: sl-n-q-lies-in-one-factor-of-every-normal-series
requires: []
---

Direct proof. Not independently reviewed. Write `e_ij(q) = I + qE_ij` for
`i ≠ j`, and `X_ij = {e_ij(q) : q in Q}`. Elementary matrices generate
`SL_n(K)` over any field `K`, by Gaussian elimination.

## Step 1. A normal subgroup of SL_n(Q) that contains one root element is everything

Let `M` be normal in `SL_n(Q)` and suppose `e_ij(q) in M` with `q ≠ 0`.

- **Every multiple.**
  - If `n >= 3`, pick `k` not in `{i,j}` and put `d = diag` with `d_i = lambda`,
    `d_k = lambda^-1`, and all other entries 1. Then `d` is in `SL_n(Q)` and
    `d e_ij(q) d^-1 = e_ij(lambda q)`. So `X_ij <= M`.
  - If `n = 2`, `diag(a, a^-1) e_12(q) diag(a, a^-1)^-1 = e_12(a^2 q)`. Every
    positive rational `r` is a sum of four rational squares: `r = u/v = uv/v^2`,
    and `uv` is a sum of four integer squares by Lagrange's theorem. Hence
    `e_12(rq)` is a product of four elements of `M`, and `e_12(-rq)` is its
    inverse. So `X_12 <= M`, and the case `X_21` is symmetric.
- **Every root group.** A permutation matrix with one sign changed to make the
  determinant 1 lies in `SL_n(Q)` and conjugates `X_ij` onto `X_(sigma i)(sigma j)`
  for any permutation `sigma`, because the sign only rescales the parameter. For
  `n = 2` use `w = [[0,1],[-1,0]]`, with `w e_12(q) w^-1 = e_21(-q)`. So every
  `X_kl <= M`.
- **Conclusion.** The `X_kl` generate `SL_n(Q)`, so `M = SL_n(Q)`.

**For `SL_n(Q)/C` with `C` central.** Let `M` be normal in `SL_n(Q)/C` and contain
a nontrivial element of the image of `X_ij`, say the image of `e_ij(q)`. The
preimage of `M` is normal in `SL_n(Q)` and contains `e_ij(q)`, so it is all of
`SL_n(Q)`, and `M` is everything.

## Step 2. SL_n(Q)/C is perfect

Given `i ≠ j`, let `h` be diagonal with `h_i = 2`, `h_j = 1/2` and all other
entries 1. Then `h e_ij(x) h^-1 = e_ij(4x)`, so the commutator
`h e_ij(x) h^-1 e_ij(x)^-1` equals `e_ij(3x)`. Taking `x = q/3` shows that every
`e_ij(q)` is a commutator. The elementary matrices generate, so `SL_n(Q)` is
perfect, and so are all of its quotients.

## Step 3. Dichotomy for one normal subgroup

Let `H = SL_n(Q)/C <= E` and let `S` be normal in `E`. Then `H ∩ S` is normal in
`H`. If it contains a nontrivial element of some `X_ij`, Step 1 gives `H <= S`.
Otherwise every `X_ij` meets `S` trivially.

## Step 4. The series

Given the series `S_0 <= ... <= S_k` of normal subgroups of `E`, let `t` be least
with `H <= S_t`. It exists because `S_k = E`, and `t >= 1` because `H ≠ 1`.

- Since `H` is not contained in `S_(t-1)`, Step 3 gives `X_ij ∩ S_(t-1) = 1`, so
  `E -> E/S_(t-1)` is injective on each `X_ij`. Its image lies in `S_t/S_(t-1)`,
  because `X_ij <= H <= S_t`. This is item 1.
- The image of `H` is `H/(H ∩ S_(t-1))`. It is nontrivial, since it contains a
  copy of `(Q,+)`, and perfect by Step 2. This is item 2.
- A nontrivial perfect group is nonabelian, and a group containing `(Q,+)` is not
  Q-free. So the factor `S_t/S_(t-1)` is neither abelian nor Q-free.

## Step 5. The listed groups

- `SL_n(Q) <= GL_n(Q)` is the case `C = 1`.
- The image of `SL_n(Q)` in `PGL_n(Q)` is `SL_n(Q)/(SL_n(Q) ∩ Q^x I)`, a quotient by
  a central subgroup. It is `PSL_n(Q)`, which lies in `PGL_n(Q)`.

So a group `E` containing any of `GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)`, `PSL_n(Q)` has
a factor that is neither abelian nor Q-free in every finite series of normal
subgroups. ∎

## Checks on the special cases

- **Solvable-by-(Q-free).** Take `S` solvable and normal with `E/S` Q-free. The
  derived series `S^(r)` consists of characteristic subgroups of `S`, which are
  therefore normal in `E`. So `1 = S^(r) <= ... <= S^(1) <= S <= E` is a series of
  normal subgroups whose factors are abelian and then `E/S`.
- **Three-term shape.** For the hypotheses of
  `lifts-add-no-unipotent-divisibility`, take the series `1 <= N <= K <= E`. Its
  factors are `N` (Q-free), `K/N` (central, hence abelian) and `E/K` (Q-free).
