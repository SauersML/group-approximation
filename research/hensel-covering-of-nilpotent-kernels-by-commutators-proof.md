---
rg: 2
id: hensel-covering-of-nilpotent-kernels-by-commutators-proof
kind: route
title: Correct one layer at a time, using that the linearized commutator map is onto exactly when no functional is fixed
target: hensel-covering-of-nilpotent-kernels-by-commutators
requires: []
---

Notation: `[x, y] = x y x^-1 y^-1`. Write `M_j` additively, with `g · m` the conjugation action.

## 1. The layer map

For `g in Q` and `gamma in K_j`, `[g, gamma] = (g gamma g^-1) gamma^-1` lies in `K_j`, with image
`(g - 1) gammabar` in `M_j`. Let `Lambda_j : M_j^s -> M_j` be `(m_i) -> sum_i (g_i - 1) m_i`.

A functional `f` on `M_j` annihilates `im Lambda_j` iff `f((g_i - 1) m) = 0` for all `i` and `m`, that is,
iff `f` is fixed by every `g_i` in the dual action. By (F), only `f = 0` annihilates `im Lambda_j`.
Since `M_j` is a finite-dimensional vector space, `Lambda_j` is onto.

## 2. Successive approximation

We show by induction on `j = 1, ..., m` that there are `beta_1, ..., beta_s in K` with
```text
eps_j := ( [g_1, beta_1] ... [g_s, beta_s] )^-1 kappa   in K_j .
```
- **Start.** For `j = 1`, take every `beta_i = 1`, so `eps_1 = kappa in K = K_1`.
- **Step.** Suppose `eps_j in K_j` with `j < m`.
  - By Section 1, choose `gamma_i in K_j` with `sum_i (g_i - 1) gammabar_i = epsbar_j` in `M_j`.
  - `[g_i, beta_i gamma_i] = [g_i, beta_i] · x_i`, where `x_i = beta_i [g_i, gamma_i] beta_i^-1 in K_j`.
  - `beta_i in K` acts trivially on `M_j`, because `[K, K_j] <= K_(j+1)`. So
    `xbar_i = (g_i - 1) gammabar_i`.
  - `M_j` is central in `K/K_(j+1)`, and each `[g_i, beta_i]` lies in `K`. So, modulo `K_(j+1)`, the new
    product is congruent to `[g_1, beta_1] ... [g_s, beta_s] · x_1 ... x_s`.
  - The new error is congruent to `(x_1 ... x_s)^-1 eps_j`, whose image in `M_j` is
    `epsbar_j - sum_i (g_i - 1) gammabar_i = 0`. So it lies in `K_(j+1)`.
- **End.** At `j = m`, `eps_m in K_m = 1`, so `kappa = [g_1, beta_1] ... [g_s, beta_s]`.

## 3. Covering form

- Let `g_i = z_i P_i` with `z_i in C_Q(K)` and `P_i in Cons_m(S)`, and let `beta in K`. Then
  `P_i beta P_i^-1 in K` commutes with `z_i`, so `[z_i P_i, beta] = [P_i, beta]`.
- `z_i` acts trivially on every layer, so (F) for the `g_i` is (F) for the `P_i`.
- `[P_i, beta] = P_i · (beta P_i^-1 beta^-1)` is a product of `2m` conjugates of elements of `S^(+-1)`.
- By Section 2, `kappa in Cons_(2sm)(S)`.

## 4. The instances

- **Congruence kernels.** `K_j = ker(SL_n(R) -> SL_n(R/m^j))` satisfy the hypotheses (part 1 of
  `simple-group-width-over-congruence-targets`, Lemma 1.1), with `M_j ≅ sl_n(F_q)`. (F) for a Singer pair
  is Lemma 2.2 there.
- **Single Singer seed on `F_q^n`, its dual and `Lambda^k`.**
  - The eigenvalues of `zeta^(q-1)` on `Lambda^k F_(q^n)` are products `zeta^((q-1)(q^(i_1) + ... + q^(i_k)))`
    over distinct exponents `i_1, ..., i_k < n`.
  - Such a product equals `1` iff `q^n - 1` divides `(q - 1)(q^(i_1) + ... + q^(i_k))`. For `1 <= k < n` this
    number is positive and below `q^n - 1`, so it never happens.
  - So there is no eigenvalue `1`, and none on the dual either. Sums of copies behave the same way.
- **Trivial model.** If all `g_i` act trivially on `M_1 != 0`, then `Lambda_1 = 0`. Every `[g_i, beta]` has
  image `(g_i - 1) betabar = 0` in `M_1`, so it lies in `K_2`, and so does the product. Elements of
  `K \ K_2` are not reached, and the conclusion fails.
