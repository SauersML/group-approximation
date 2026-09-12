---
rg: 2
id: anchored-flexible-compressions-have-zero-entropy
kind: claim
title: Sublinear padding and a diffuse pin make flexible exact representation families entropy-null
artifacts:
  - research/artifacts/flexible-packet-anchoring-2026-08-22.md
distinct_from:
  anchored-exact-wreath-packets-have-zero-entropy: that treats exact tuples already living in the target dimension; this permits exactification in a larger dimension and proves that the Stiefel/Grassmannian compression freedom disappears after diffuse anchoring.
  robust-diffuse-pin-stabilizer-has-zero-entropy: that controls the residual right-unitary gauge for one pin; this also controls the moving compression subspace and subquadratically many exact representation classes.
---

Let `d_n<=m_n` with `(m_n-d_n)/d_n -> 0`.  Fix a finite coordinate set `F`
and an operator-norm cutoff `R`.  For each `n`, let

```text
(X_(alpha,n),A_(alpha,n)) in M_(m_n)(C)^F x M_(m_n)(C)_sa,
alpha=1,...,N_n,
```

be uniformly bounded, with `log N_n=o(d_n^2)`.  Let `D_n in M_(d_n)(C)_sa`
be a uniformly bounded diffuse microstate pin, and let `eta_n->0`.  Define
`Omega_n` to consist of all compressed tuples

```text
V^* X_(alpha,n) V,
```

where `V:C^(d_n)->C^(m_n)` is an isometry and

```text
||V^* A_(alpha,n) V-D_n||_2<=eta_n.                     (AFC1)
```

Then for every fixed `epsilon>0`,

```text
limsup_n d_n^(-2) log K_epsilon(Omega_n,||.||_2)=0.     (AFC2)
```

Thus flexible exactification with `o(d_n)` padding creates no quadratic
anchored moduli, even though the unanchored Stiefel manifold has order
`d_n^2` real dimension.
