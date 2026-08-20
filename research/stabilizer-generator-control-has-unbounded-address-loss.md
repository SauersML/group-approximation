---
rg: 2
id: stabilizer-generator-control-has-unbounded-address-loss
kind: claim
title: Conjugacy-compressed checks can still lose unboundedly through stabilizer naming
artifacts:
  - research/artifacts/conjugacy-addressed-machine-groupification-audit-2026-08-20.md
distinct_from:
  conjugacy-compressed-dimension-trigger: that proves exact zero-loss transport for a relator once its address word is fixed; this proves that choosing coherent address words for one coset cell has an independent, potentially unbounded stabilizer cost.
  uniform-hs-site-coherence-for-finite-bi-index-pair: that asks for additional rounding and spectral-gap structure giving uniform coherence; this is the unconditional obstruction showing why finite stabilizer generators alone do not suffice.
---

Let `G` be a group, let `H=<T>` be a finitely generated subgroup, and let
`U:G -> U(d)` be a unitary representation.  Transport a root observable
`A in U(d)` to the left-coset cell `gH` by

```text
A_(gH)=U_g A U_g^*.
```

If `g'=gh` is another name for the same cell, then unitary invariance gives

```text
||U_g A U_g^* - U_(g') A U_(g')^*||_2
  = ||A-U_h A U_h^*||_2.                                  (SGL1)
```

For a shortest expression `h=t_1...t_L`, repeated insertion and conjugation
give the telescoping estimate

```text
||A-U_h A U_h^*||_2
 <= sum_(i=1)^L ||A-U_(t_i) A U_(t_i)^*||_2
 <= |h|_T max_(t in T union T^-1) ||A-U_t A U_t^*||_2.      (SGL2)
```

There is no constant independent of `h` that can replace `|h|_T` using only
the generator defects.  Already take `H=Z=<t>` on `C^2`, put

```text
A=sigma_z,                  U_t=exp(i theta sigma_x/2).
```

With normalized Hilbert--Schmidt norm,

```text
||A-Ad(U_t)(A)||_2       =2|sin(theta/2)|,
||A-Ad(U_(t^L))(A)||_2   =2|sin(L theta/2)|.               (SGL3)
```

Choosing `theta=L^-2` makes the ratio in `(SGL3)` tend to `L`.  Thus control
on a finite stabilizer generating set does not imply uniform coset-site
coherence, even for exact representations of the ambient words.

The machine consequence is precise.  Literal conjugate copies of prototype
checks incur no runtime loss, but a tape encoded as `G/H` still needs an
additional mechanism making the root observable uniformly `H`-invariant.
Same-dimension stability plus an adjoint Kazhdan gap is one sufficient package
(`hs-stable-kazhdan-finite-bi-index-pair-gives-site-coherence`); raw orbit
addressing is not.
