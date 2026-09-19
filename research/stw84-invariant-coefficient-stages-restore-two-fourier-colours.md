---
rg: 2
id: stw84-invariant-coefficient-stages-restore-two-fourier-colours
kind: claim
title: Invariant and coherently inner coefficient stages restore two Fourier colours
distinct_from:
  stw84-scalar-fourier-row-two-colour: that theorem factors scalar rows through the circle; the present theorem treats matrix coefficients by replacing the circle with the finite-dimensional coefficient crossed product and gives a perturbative local criterion beyond exact invariant stages.
artifacts:
  - research/artifacts/stw84-invariant-coefficient-two-colour-audit-2026-08-30.md
---

Let `B` be a unital C-star algebra, let `alpha in Aut(B)`, and put

```text
A=B rtimes_alpha Z,
```

with implementing unitary `U`.  Let `D subset B` be a finite-dimensional
unital `alpha`-invariant subalgebra.  For `n>=1` define

```text
Sigma_(D,n):M_n(D)->C*(D,U),
Sigma_(D,n)([d_ij])
 =n^(-1)sum_(i,j=0)^(n-1) U^i d_ij U^(-j).            (ICF1)
```

This map is c.p.c., and

```text
dim_nuc(C*(D,U))<=1.                                   (ICF2)
```

If `h in A` is a positive contraction which commutes with `D`, then, for
every finite `E subset M_n(D)` and `epsilon>0`, there is `delta>0` such
that

```text
||[h,U]||<delta                                        (ICF3)
```

implies that the weighted coefficient row

```text
C_h o Sigma_(D,n):c |-> h^(1/2)Sigma_(D,n)(c)h^(1/2)  (ICF4)
```

has an `epsilon`-accurate finite-dimensional approximation on `E` with two
c.p.c. order-zero return colours.

There is also a perturbative global consequence.  Say that `alpha` has
**coherently inner finite stages** if, for every finite `F subset B` and
`delta>0`, there are a finite-dimensional unital subalgebra `D subset B`
and a unitary `v in D` such that

```text
dist(a,D)<delta                         (a in F),
sup_(d in D, ||d||<=1)||alpha(d)-v d v^*||<delta.      (ICF5)
```

Then

```text
dim_nuc(B rtimes_alpha Z)<=1.                          (ICF6)
```

No invariant exhaustion is required in `(ICF5)`.  The uniformity on the
whole stage, including its implementing unitary `v`, is the coherence that
allows the almost-commuting residual Fourier unitary to be replaced by an
exactly commuting one.

For a group-AF coefficient algebra `B=C*(K)`, exact invariant finite
subgroup stages fall under `(ICF1)--(ICF4)`, recovering two colours for
their cyclic crossed products and their augmentation ideals.  They need
not satisfy `(ICF5)`, since the induced automorphism may permute matrix
summands and therefore be outer on the finite-dimensional algebra.  In the
general locally finite-by-cyclic problem, orbit-window subgroups are finite
but need not be invariant and no coherent implementer as in `(ICF5)` is
known.  This is the precise coefficient-covariance obstruction left after
the scalar-row theorem.
