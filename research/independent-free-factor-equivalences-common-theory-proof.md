---
rg: 2
id: independent-free-factor-equivalences-common-theory-proof
kind: route
title: Direct proof that log-independent free factor equivalences force a common theory
target: independent-free-factor-equivalences-force-common-theory
requires:
  - interpolated-free-group-factor-compression-formula
  - first-order-fundamental-group-closed-under-amplification
---

**Notation.** `M := L(F_2)`, `c(r) := (r-1)^{-1/2}` for `1 < r < infinity`. By
`interpolated-free-group-factor-compression-formula` with `r = 2`,
`M_gamma = L(F_{1 + 1/gamma^2})`. Since `1 + 1/c(r)^2 = r`, we get
`L(F_r) = M_{c(r)}` (isomorphism). Isomorphic factors are elementarily
equivalent, and `≡` is an equivalence relation.

**Step 1: one comparison gives an element of `F_fo(M)`.** Suppose
`L(F_m) ≡ L(F_n)`, so `M_{c(m)} ≡ M_{c(n)}`. By item 2 of
`first-order-fundamental-group-closed-under-amplification`, amplifying both by
`t = 1/c(m)` preserves `≡`. With `(M_a)_b = M_{ab}` (Dykema),

```text
M = M_1 = (M_{c(m)})_{1/c(m)}  ≡  (M_{c(n)})_{1/c(m)} = M_{gamma},
gamma := c(n)/c(m) = sqrt((m-1)/(n-1)).
```

So `gamma in F_fo(M)`, and `gamma != 1` since `m != n`.

**Step 2: part 1.** `F_fo(M)` is a group (item 1), so `gamma^k in F_fo(M)` and
`M ≡ M_{gamma^k}` for all `k in Z`. Amplify by `c(r)` (item 2):
`M_{c(r)} ≡ M_{c(r) gamma^k}`. Put `c(s) = c(r) gamma^k`. Then
`(s-1)^{-1/2} = (r-1)^{-1/2} gamma^k`, so `s - 1 = (r-1) gamma^{-2k} = (r-1)((n-1)/(m-1))^k`.
Hence `L(F_r) ≡ L(F_{1+(r-1)lambda^k})` with `lambda = (n-1)/(m-1)`.

**Step 3: part 2.** Step 1 gives `gamma_1, gamma_2 in F_fo(M)`, where
`gamma_i = sqrt((m_i-1)/(n_i-1))`. Put `a = log gamma_1` and `b = log gamma_2`;
both are nonzero, and `a/b = log((m_1-1)/(n_1-1)) / log((m_2-1)/(n_2-1))` is
irrational (the factors 1/2 cancel).

- `log : (R_+, ·) -> (R, +)` is an isomorphism of topological groups, so
  `H := log F_fo(M)` is a closed subgroup of `R` (item 1) containing `a` and `b`.
- A subgroup of `R` is either cyclic (`dZ`, possibly `0`) or dense. If `H = dZ`,
  then `a = pd` and `b = qd` with `p, q in Z` and `q != 0`, so `a/b = p/q` would
  be rational. Contradiction. So `H` is dense.
- `H` is closed and dense, so `H = R` and `F_fo(M) = R_+`.

**Step 4: common theory.** For `1 < r, s < infinity`:
`L(F_r) = M_{c(r)} ≡ M ≡ M_{c(s)} = L(F_s)`, using `c(r), c(s) in F_fo(M)`.
Also `F_fo(L(F_r)) = R_+`: for `t in R_+`,
`(M_{c(r)})_t = M_{c(r) t} ≡ M ≡ M_{c(r)}`.

**Step 5: part 3.** Take `(m_1, n_1) = (2, 3)` and `(m_2, n_2) = (2, 4)`. The
ratio is `log(1/2)/log(1/3) = log 2/log 3`. If it equalled `p/q` with integers
`q > 0`, then `2^q = 3^p`, forcing `p = q = 0` by unique factorization. So it is
irrational, and part 2 applies.

Inputs used, statement level only: Dykema Theorem 2.4 and
`(M_{gamma_1})_{gamma_2} = M_{gamma_1 gamma_2}`; Goldbring–Hart closedness of
`F_fo`; the Goldbring–Pi amplification lemma. The remaining steps are
elementary and complete here.
