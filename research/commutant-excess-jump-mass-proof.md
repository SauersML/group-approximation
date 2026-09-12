---
rg: 2
id: commutant-excess-jump-mass-proof
kind: route
title: Low aspect-ratio pairs are almost-irreducible restrictions matched one to one, so only the jump mass carries excess
target: commutant-excess-bounded-by-aspect-ratio-jump-mass
requires: []
artifacts:
  - research/artifacts/hs-scale-pinning-2026-09-12.md
---

**Setup.** Decompose `C^n = sum_(i,j) H_ij`, with `H_ij = C^(m_i) (x) C^(c_ij) (x) W_j` and
`W_j` the space of `theta_j`. Both `zeta_A = m_i/d_i` and `zeta_B = m'_j/e_j` are constant
on `H_ij`, and they commute. Since `m'_j >= m_i c_ij` and `d_i >= c_ij e_j`, the ratio
satisfies

```text
R_ij = m'_j d_i / (m_i e_j) >= c_ij^2 >= 1.
```

**Low pairs.** Call `(i,j)` low if `R_ij < 1 + c`, with `c < 1`. Then:
- `c_ij = 1`;
- `sum_(i' != i) m_(i') c_(i'j) < c m_i`, from `m'_j < (1+c) m_i e_j/d_i <= (1+c) m_i`;
- `d_i - e_j < c e_j`, from `d_i < (1+c) m_i e_j/m'_j <= (1+c) e_j`.

Low pairs form a partial matching:
- two low partners `j != j'` of one `i` would give `e_j + e_(j') > 2 d_i/(1+c) > d_i`;
- two low partners `i != i'` of one `j` would give `m_i + m_(i') > m'_j`.

**Estimate.** Let `P` be the projection onto the sum of the low `H_ij`. Then
`tau(1 - P) = tau(zeta_B >= (1+c) zeta_A)`. Take `x in B` with `||x|| <= 1`. Since
`||x - E_A x|| <= 2`,

```text
||x - E_A x||_2 <= ||(1-P)(x - E_A x)||_2 + ||P(x - E_A x)(1-P)||_2 + ||P(x - E_A x)P||_2
               <= 4 tau(1-P)^(1/2) + ||P(x - E_A x)P||_2.
```

- `x = sum_j x_j (x) 1_(W_j)` with `x_j` acting on `K_j = sum_i C^(m_i) (x) C^(c_ij)`. For low
  pairs, `j` determines `i`. So `P x P = sum_low x_j^(i,i) (x) 1_(W_j)` on
  `C^(m_i) (x) W_j`.
- `E_A x = sum_i y_i (x) 1_(V_i)`, where
  `y_i = d_i^(-1) sum_(j') e_(j') Tr_(C^(c_ij'))(x_(j')^(i,i))`. So
  `P E_A(x) P = sum_low y_i (x) 1_(W_j)`.
- For a low pair, `y_i - x_j^(i,i) = (e_j/d_i - 1) x_j^(i,i) + d_i^(-1) sum_(j' != j) (...)`.
  The two terms have total weight at most `2 (d_i - e_j)/d_i < 2c` in operator norm.
- Hence

```text
||P(x - E_A x)P||_2^2 <= n^(-1) sum_low m_i e_j (2c)^2 <= 4c^2,
```

and the bound follows.

**Monotonicity.** `zeta_B >= zeta_A` because `R_ij >= 1` on every piece.
