---
rg: 2
id: schur-toeplitz-head-matrix-amplification-proof
kind: route
title: Multiply packet-valued Toeplitz matrix units and expand the iterated compressor
target: schur-toeplitz-head-is-matrix-amplified-forbidden-algebra
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
  - schur-toeplitz-envelope-has-proper-self-embedding
---

For `a,b in A_f^-`, the relations `P_fx=0`, `yP_f=0`, and `yx=1` give

```text
(x^iay^j)(x^kby^l)=delta_(jk)x^i(ab)y^l.
```

If `j<k`, a positive power of `x` meets the right support `P_f` of `a`; if
`j>k`, a positive power of `y` meets the left support `P_f` of `b`; both
products vanish. Sandwiching a linear relation by `e_i,e_j` isolates its
`(i,j)` coefficient, and multiplication on the left by `y^i` and on the
right by `x^j` recovers that coefficient in the already embedded algebra
`A_f^-`. Thus the matrix-coefficient map is injective, proving `(SHM2)`.

Formula `(SHM3)` follows by induction from
`sigma(r)=xry+epsilon(r)P_f` and `epsilon sigma=epsilon`. Multiplication by a
head coefficient kills the `x^Nr y^N` term on either side and the diagonal
sum acts as the unit on all first-`N` matrix rows and columns. This gives
`(SHM4)`.
