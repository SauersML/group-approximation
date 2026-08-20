---
rg: 2
id: subsqrt-word-windows-miss-hs-gap-collapse
kind: claim
title: Sub-square-root word windows cannot detect the rank-one HS gap collapse
---

There are dimensions `d_n -> infinity`, an exact irreducible representation
`rho_n` of a property-`(T)` group on `C^(d_n)`, and an irreducible unitary
generator tuple `V_n` such that

```text
max_(s in S) ||V_(s,n)-rho_n(s)||_2 = O(d_n^(-1/2)),
```

the adjoint Poincare constant of `rho_n` is bounded below uniformly, while the
adjoint Poincare constant of `V_n` tends to zero.  Moreover, for every integer
sequence `L_n=o(sqrt(d_n))`,

```text
sup_(formal words w with |w|<=L_n)
  ||w(V_n)-rho_n(w)||_2 -> 0.
```

Thus even an adaptively growing collection of all word tests up to
sub-square-root length cannot certify a scalar adjoint gap on an irreducible
normalized-HS almost-representation block.  A successful HS-Kun selection
principle must either inspect genuinely spectral/support information or use a
word scale at least comparable to the inverse generator-perturbation scale.

## Attempts

- Combine the rank-one surgery construction with uniform word telescoping;
  the bound is linear in word length and `O(d^(-1/2))` per generator.
