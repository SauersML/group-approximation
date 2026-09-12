---
rg: 2
id: kazhdan-rank-rounding-over-every-field-proof
kind: route
title: Truncate polynomial degree in the representations of EL_3(Z[t]) over F[x]/(f)
target: kazhdan-rank-rounding-fails-over-every-field
requires: []
artifacts:
  - research/artifacts/weakly-sofic-extension-metric-scope-2026-09-12.md
---

## Literature input

Ershov--Jaikin-Zapirain, *Property (T) for noncommutative universal lattices*, Invent.
Math. **179** (2010) 303--347, arXiv:0809.4095, Theorem 1.1: `EL_n(R)` has property (T)
for `n >= 3` and every finitely generated unital associative ring `R`. With `R = Z[t]`,
`Gamma = EL_3(Z[t])` is Kazhdan, and its finite generating set `S` is a Kazhdan set.

## Why sufficient

Sections 2 and 3 of the artifact. The rest is linear algebra.

- **Generation.** `[x_ik(t^a), x_kj(t^b)] = x_ij(t^(a+b))` for distinct `i, k, j`, so `S`
  generates `Gamma`.
- **Invariant subspaces (Lemma 2.1).**
  - `rho(x_ij(t^k)) - 1 = E_ij (x) x^k`, and the products `(E_ij (x) x^k)(E_ji (x) 1)` give
    the diagonal units.
  - So an invariant subspace is an `M_3(A)`-submodule of `A^3`, `A = F[x]/(f)`, hence
    equals `I^3` for an ideal `I = gA`, with `g | f` and `dim I = N - deg g`.
- **Almost invariance (Lemma 2.2).** `x_ij(1)` preserves `W_m`, and `x_ij(t)` maps it into
  `W_m + F x^m e_i`.
- **Distance (Lemma 2.3).**
  - `dim(S_m n gA) = max(0, m - deg g)`, because a polynomial of degree `< m <= N-1` lies
    in `gA` iff `g` divides it.
  - This gives `d(W_m, (gA)^3) >= 3 min(m, N - m)`.
- **Irreducibility over `Q`.** `x^N - 2` is Eisenstein at `2`, so `A` is a field and the
  only ideals are `0` and `A`.
- **Commutator bound.** `[pi_m, x]` is nonzero only on `x^(m-1)` and `x^(N-1)`, so
  `rank [P_m, 1 + E_ij (x) x] <= 2`. The classes of `P_(floor(beta N))` form the chain.
