---
rg: 2
id: stw84-circle-factor-row-proof
kind: route
title: Factor the row through the circle and repair quasicentral cutdowns of its two colours
target: stw84-scalar-fourier-row-two-colour
requires:
  - stw84-weighted-fourier-cutdown-and-row-gap
  - stw82-quasicentral-cutdowns-repair-to-banded-order-zero
artifacts:
  - research/artifacts/stw84-scalar-fourier-row-two-colour-audit-2026-08-30.md
---

## 1. Exact symbol factorization

Define a u.c.p. map

```text
sigma_n:M_n->C(T),
sigma_n([c_ij])(z)=n^(-1)sum_(i,j)c_ij z^(i-j).         (SMF5)
```

Indeed, at `z in T` this is compression by the unit vector

```text
n^(-1/2)(1,z^(-1),...,z^(-(n-1))).
```

Let `kappa:C(T)->A` be the unital star-homomorphism determined by
`kappa(z)=U`, and put

```text
eta_h(f)=h^(1/2)kappa(f)h^(1/2).                       (SMF6)
```

Then `eta_h` is c.p.c. and direct substitution gives the exact identity

```text
Theta_(h,n)=eta_h o sigma_n.                           (SMF7)
```

On diagonal matrices `sigma_n` is the scalar average, proving `(SMF4)`.

## 2. Use the two colours of the circle

Fix finite `E subset M_n` and `epsilon>0`.  Since
`dim_nuc(C(T))=1`, choose

```text
C(T) --psi--> F_0 direct_sum F_1
     --(phi_0+phi_1)--> C(T)                           (SMF8)
```

which approximates `sigma_n(E)` sufficiently closely, where `psi` is
c.p.c. and each `phi_l` is c.p.c. order zero.  Put

```text
pi_l=kappa o phi_l:F_l->A.
```

These are c.p.c. order-zero maps.

The unit balls of the finite-dimensional spaces `phi_l(F_l)` form compact
subsets of `C(T)`.  Approximate them uniformly by trigonometric polynomials
of one common degree.  Since

```text
||[h,U^k]||<=|k| ||[h,U]||,                            (SMF9)
```

condition `(SMF2)`, with `delta` sufficiently small, gives

```text
sup_(z in (F_l)_1)||[h,pi_l(z)]||<gamma               (SMF10)
```

for both colours, where `gamma` is as small as required below.

## 3. Repair the cut colours

Define c.p.c. maps

```text
theta_l(z)=h^(1/2)pi_l(z)h^(1/2).                      (SMF11)
```

If `x,y` are orthogonal positive contractions in `F_l`, then

```text
theta_l(x)theta_l(y)
 =h^(1/2)pi_l(x)[h,pi_l(y)]h^(1/2),                   (SMF12)
```

because `pi_l(x)pi_l(y)=0`.  Thus `(SMF10)` makes the order-zero defect
uniformly small.  Uniform stability of c.p.c. order-zero maps on a fixed
finite-dimensional domain supplies c.p.c. order-zero maps

```text
rho_l:F_l->A
```

arbitrarily close to `theta_l`.  This is the same cone-projective repair
used in `stw82-quasicentral-cutdowns-repair-to-banded-order-zero`.

For `c in E`, equations `(SMF7)--(SMF8)` and contractivity of `eta_h` show
that

```text
sum_l theta_l(psi(sigma_n(c))_l)
```

is close to `Theta_(h,n)(c)`.  Replacing the two `theta_l` by `rho_l`
adds only the two chosen repair errors.  Taking all preliminary tolerances
small proves the asserted two-colour approximation.

The argument is uniform in `A`, `U`, and `h` after the finite set, its
circle approximation, and the tolerance are fixed.  It does not extend
formally to coefficient-valued matrices: covariance prevents the
coefficient symbol from being followed by a star-homomorphism analogous to
`kappa`.
