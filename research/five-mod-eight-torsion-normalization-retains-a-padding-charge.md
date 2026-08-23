---
rg: 2
id: five-mod-eight-torsion-normalization-retains-a-padding-charge
kind: claim
title: Five-mod-eight Weil packets retain constant structural energy after exact torsion normalization
distinct_from:
  even-weil-second-cubic-has-a-rank-six-determinant-gap: that places the determinant charge in the approximate second cubic before torsion normalization; this transports a determinant charge to the BS structural word after all three torsion rows are exact.
  direct-sum-weil-compressions-have-quadratic-padding: that proves the energy ledger in square-free BS coordinates; this proves it in the exact C2 star C3 star C3 frame requested by the terminal quotient-lifting problem.
  exact-torsion-frame-has-rank-one-strict-counterpackets: that gives an upper defect bound and strict separation for every prime one modulo four; this supplies a matching positive unnormalized-energy lower bound on the five-modulo-eight subfamily.
---

For every prime `p=5 mod 8`, apply the two-triangle torsion normalization
blockwise to the compressed even-Weil tuple and write the resulting exact
torsion frame as

```text
rho_p:<X,A,B | X^2=A^3=B^3=1> -> U((p-1)/2).
```

For the structural words `(ETF2)--(ETF3)`, put

```text
u=(XR)^2,
v=RTR^(-1)T^(-4),       T=XA,       R=A^2XA^2B.
```

Then

```text
rank(rho_p(v)-1)<=46,          det(rho_p(v))=-1,      (FNT1)
||rho_p(v)-1||_F^2>=2/23.                              (FNT2)
```

Thus one restored Weil line is paid by the **post-normalization structural
energy**:

```text
1 <= (23/2)(||rho_p(u)-1||_F^2+||rho_p(v)-1||_F^2).  (FNT3)
```

For an orthogonal sum of `K` such packets, using the same blockwise spectral
rounding,

```text
K <= (23/2) E_structural.                             (FNT4)
```

Restoring the `K` deleted fixed lines gives an exact quotient
representation.  The estimate is unchanged by a common unitary mixing of
the summands, since functional calculus and Frobenius energy are unitarily
equivariant.

This is a genuine positive instance of the sharp flexible torsion-frame
ledger.  It shows that moving all error out of the cubic rows and into the
two structural words does not erase the quadratic padding charge.  It does
not handle determinant-neutral primes or arbitrary cross-packet tuples not
known to arise from a finite-rank compression.
