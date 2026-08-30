---
rg: 2
id: stw74-homogeneous-fibre-support-descent-proof
kind: route
title: Extract the compact-open support of a matrix-bundle projection
target: stw74-homogeneous-coefficient-projections-descend
requires:
  - stw74-property-sp-is-the-exact-missing-condition
  - stw74-every-nonzero-cu-class-is-a-finite-unit-root
---

Let `p=(p_ij) in M_n(B)` have coefficient algebra `C` homogeneous of
finite degree `r`.  Use the standard structure theorem for homogeneous
C*-algebras: there are a locally compact Hausdorff space `X` and a locally
trivial C*-bundle `E` over `X`, with fibre `M_r(C)`, such that

```text
C ~= Gamma_0(X,E).
```

Under this identification `p in M_n(C)` is a continuous section of the
matrix bundle `M_n(E)` and every fibre `p(x)` is a projection.  Hence

```text
||p(x)|| in {0,1}.
```

Its nonzero set

```text
K={x in X : p(x)!=0}
```

is both open and closed by norm continuity.  It is compact because `p`
vanishes at infinity: `K={x:||p(x)||>=1/2}`.  Since `p!=0`, the set `K` is
nonempty.

Let `q` be the section of `E` which is the fibre identity on `K` and zero
off `K`.  The compact-open property makes this section continuous and
vanishing at infinity, so

```text
0!=q=1_K 1_E in Gamma_0(X,E)=C.
```

It is a central projection.  This proves the level-one descent lemma.  When
`r=1`, the same projection is the positive support of the integer-valued
ordinary matrix trace `sum_i p_ii`.

Apply the lemma with `B=H` in `(HF)`.  It puts a nonzero projection inside
every nonzero hereditary subalgebra `H` of `A`, which is property (SP).  The
established exact LXXIV property-(SP) theorem then makes `A` purely infinite.
The finite-unit-root theorem explains why `(HF)` adds no existence assumption
at the stabilized level: for `0!=a in H_+`, some finite multiple of `[a]`
is the compact unit class, so a nonzero projection occurs in a finite matrix
algebra over `Her_A(a) subset H`.

Finally, if `D` is projectionless, the first paragraph rules out a
finite-degree homogeneous coefficient algebra for every nonzero stabilized
projection over `D`.  For a scalar unitary `U in M_n(C)`, each coefficient
of `U* p U` is a complex linear combination of the coefficients of `p`, and
applying `U` instead of `U*` gives the reverse inclusion.  Hence the
generated coefficient algebra is unchanged by scalar basis rotation.  The
obstruction is intrinsic to the finite projective module, not an artefact of
its chosen coordinate frame.

No comparison, cancellation, property (QQ), algebraicity, separability, or
nuclear regularity is used.
