---
rg: 2
id: leavitt-unit-frobenius-bounded-threshold-iff-fb-rigidity
kind: claim
title: The bounded-block threshold for the binary Leavitt unit group extends to bounded block size times squared defect exactly when Frobenius-bounded models are trivial
distinct_from:
  leavitt-unit-bounded-block-models-are-asymptotically-trivial: that proves asymptotic triviality when block size times squared defect tends to zero, which is operator-norm control on most blocks; this identifies the next regime, block size times squared defect bounded, and proves it is equivalent to one open statement about single-block models.
  leavitt-unit-frobenius-bounded-models-are-trivial: that is the open single-block rigidity statement; this is the established equivalence between it and the extended threshold, with no claim that either side holds.
  binary-leavitt-unit-group-hyperlinear: that asks for Hilbert--Schmidt models with no defect scale at all; this concerns only models whose unnormalized Frobenius defects stay bounded.
---

**ESTABLISHED.**  Let `R = L_(F_2)(1,2)` and `U = R^x`.  Use the block-monomial
setting of `leavitt-unit-bounded-block-models-are-asymptotically-trivial`:
maps `rho_m : U -> U(k_m) wr S_(n_m)` on `C^(n_m) ⊗ C^(k_m)` with normalized
Hilbert--Schmidt norm and defects
`eps_m(g,h) = ||rho_m(gh) - rho_m(g) rho_m(h)||_2`.  For a matrix `X` in
`M_k(C)` write `||X||_F = Tr(X^* X)^(1/2)` for the unnormalized Frobenius norm,
so `||X||_(2,k) = k^(-1/2) ||X||_F`.

The following are equivalent.

**(A) Extended threshold.**  Every block-monomial model with

```text
eps_m(g,h) -> 0   and   sup_m k_m * eps_m(g,h)^2 < infinity     for all g, h in U   (BB')
```

satisfies `||rho_m(g) - 1||_2 -> 0` for every `g in U`.

**(B) Frobenius-bounded rigidity** (`leavitt-unit-frobenius-bounded-models-are-trivial`).
For every sequence `k_L -> infinity` and maps `phi_L : U -> U(k_L)` with

```text
limsup_L ||phi_L(gh) - phi_L(g) phi_L(h)||_F < infinity          for all g, h in U,   (FB)
```

one has `||phi_L(g) - 1||_(2,k_L) -> 0` for every `g in U`.

So the landed threshold `k_m eps_m^2 -> 0` moves up to `k_m eps_m^2 = O(1)`
if and only if (B) holds, and (B) mentions a single block and no permutation
skeleton.

**What (BB') says about a block.**  On a block of size `k`, normalized defect
`delta` with `k delta^2 <= C` means unnormalized Frobenius defect at most
`sqrt(C)`.  By Markov over singular values, such a defect is at most `t` in
operator norm off a subspace of absolute dimension at most `C / t^2`.  So (BB')
is the regime "operator-norm small off a bounded number of dimensions", strictly
between operator-norm asymptotic representations, where full MF radical already
forces triviality, and arbitrary Hilbert--Schmidt models.

**Where (B) sits.**  See `leavitt-unit-frobenius-bounded-models-are-trivial`
for the sandwich: non-hyperlinearity of `U` implies (B), and (B) implies the
Frobenius-to-zero case already proved.

## Attempts

Established; see `leavitt-unit-fb-threshold-equivalence-proof`.
