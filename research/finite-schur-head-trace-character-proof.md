---
rg: 2
id: finite-schur-head-trace-character-proof
kind: route
title: Apply one Wedderburn-block matrix trace across the complete Toeplitz head
target: finite-schur-head-has-trace-character-escape
requires:
  - schur-toeplitz-head-is-matrix-amplified-forbidden-algebra
  - schur-idempotent-is-an-injective-toeplitz-defect
---

Choose one forbidden selector block of `A_f^-`. It is a full matrix algebra
`M_d(k)`, where `d` is a power of two (`D` or `2D`). Since `char(k)=p` is
odd, `d` is nonzero in `k`. Projection to this Wedderburn block followed by
the ordinary matrix trace on

```text
M_N(M_d(k))=M_(Nd)(k)
```

defines a `k`-linear functional `T_N:F_N^-->k`. It satisfies

```text
T_N(uau^-1)=T_N(a)                                        (FTP1)
```

for every unit `u`, by cyclicity of matrix trace.

Choose an `F_p`-linear functional `ell:k->F_p` for which `ell(d)!=0`; such a
functional exists because `d!=0` in `k`. Put

```text
chi_N(a)=exp(2 pi i ell(T_N(a))/p).                       (FTP2)
```

This is an additive character, and `(FTP1)` proves its invariance under the
whole head unit group.

Under the matrix-head identification, `e_i=x^iP_fy^i` is the diagonal matrix
unit `E_ii` tensored with the identity of every forbidden Wedderburn block.
On the selected block,

```text
T_N(e_i)=d.
```

Therefore `chi_N(e_i)!=1` for every `i<N`. Packet covariance and every
Reynolds averaging operation are convex combinations of inner conjugations,
so they fix this character exactly. This proves all three clauses.

