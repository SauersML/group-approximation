---
rg: 2
id: steinberg-shear-fixed-labels-recover-ideal-dimension
kind: claim
title: Pointwise-fixed Plancherel labels recover coefficient-ideal dimension, but only logarithmically
distinct_from:
  steinberg-root-shear-plancherel-covariance: That identifies the Fourier PVM and shear permutation on an arbitrary finite window; this computes the fixed-label statistic when the window is a finite-dimensional coefficient algebra.
  orthogonal-steinberg-root-spectral-support-is-not-additive: That shows the support of each individual coefficient root is not additive; this gives a different additive invariant obtained from the full multiplication shear, after taking a logarithm.
  plancherel-root-shears-have-no-compression-pressure: That proves full shear permutations preserve Plancherel mass; this identifies exactly what those stationary permutations still remember and why it is not a physical carrier mass.
---

**ESTABLISHED.**  Let `A` be an `n`-dimensional unital algebra over
`F_p`.  In `St_m(A)`, with `m>=3`, put

```text
H={x_12(a)x_13(c):a,c in A}=A direct_sum A
```

and, for `r in A`, let `q_r=x_23(r)`.  Conjugation by `q_r` induces the
shear

```text
alpha_r(a,c)=(a,c+ar).                                  (SFD1)
```

Index the Fourier atoms of `H` by `(phi,psi) in A^* direct_sum A^*`.
The atom `(phi,psi)` is fixed pointwise by the dual shear precisely when

```text
psi(ar)=0 for every a in A.                             (SFD2)
```

If `s(r)=dim_(F_p)(Ar)`, the number and Plancherel proportion of such
labels are therefore

```text
#Fix(alpha_r^*)=p^(2n-s(r)),
#Fix(alpha_r^*)/|dual(H)|=p^(-s(r)).                    (SFD3)
```

Consequently, in every canonical normalized-HS microstate on this fixed
finite table, finite-group exactification gives one Fourier projection
`F_r` (the sum of the pointwise-fixed atoms) satisfying

```text
tr(F_r)=p^(-s(r))+o(1),
||[F_r,rho(q_r)]||_2=o(1).                              (SFD4)
```

All constants depend only on the fixed algebra table, never on the matrix
dimension.

This projection is already an ordinary Reynolds projection.  For

```text
L_r={x_13(ar):a in A}<=H,                               (SFD4a)
```

a Fourier label is trivial on `L_r` exactly when `(SFD2)` holds, so

```text
F_r=e_(L_r).                                            (SFD4b)
```

For orthogonal idempotents `e,f in A`,

```text
ef=fe=0,
A(e+f)=Ae direct_sum Af.                                (SFD5)
```

Hence

```text
s(e+f)=s(e)+s(f),
tr(F_(e+f))=tr(F_e)tr(F_f)+o(1).                        (SFD6)
```

Equivalently, the logarithmic statistic

```text
dim_shear(r)=-log_p(tr(F_r))                            (SFD7)
```

recovers the algebraic left-ideal dimension and is additive on orthogonal
idempotents.

This does **not** establish the Morita-trace face needed for the
nonhyperlinearity route.  The projections satisfy

```text
F_(e+f)=F_e meet F_f                                   (SFD8)
```

inside the common Fourier algebra; they do not form a disjoint union.
Thus ordinary normalized trace is multiplicative in `(SFD6)`, while the
needed physical carrier law is additive.  Moreover `(SFD3)` is fixed by the
finite coefficient table and carries no information about the mass of a
representation-dependent shared-BCS corner.  The result identifies the
strongest coefficient-rank datum available from a full stationary
Plancherel shear table: it recovers algebraic dimension after a logarithm,
but it does not perform prescribed-carrier source coupling.  In particular,
subgroup-HNN machinery can already charge differences between the
`e_(L_r)` once the relevant coefficient ideal has been physically located;
it cannot locate that ideal on the BCS carrier.

DERIVATION
steinberg-shear-fixed-labels-dimension-proof
