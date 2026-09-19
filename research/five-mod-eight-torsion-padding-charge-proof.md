---
rg: 2
id: five-mod-eight-torsion-padding-charge-proof
kind: route
title: Track the Fourier determinant through bounded-rank cube-root rounding
target: five-mod-eight-torsion-normalization-retains-a-padding-charge
requires:
  - even-weil-second-cubic-has-a-rank-six-determinant-gap
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
  - iwahori-two-triangle-torsion-normal-form
  - exact-torsion-frame-has-rank-one-strict-counterpackets
---

Let `(X,R,T)` be the compressed even-Weil tuple before torsion
normalization.  Its first and second cubic residuals have ranks at most two
and six, respectively.  The first bound is the rank-two spectrum in
`deleted-fixed-line-first-cubic-has-explicit-positive-spectrum`; the second
is `(WCG2)`.  Also inversion and BS covariance are exact.

Put `A_old=XT`.  Nearest cube-root functional calculus changes a unitary
only on the support of its cubic residual.  Hence its rounded cube root
`A` satisfies

```text
rank(A-A_old)<=2,             rank(T_1-T)<=2,
T_1=XA.                                                     (FNP1)
```

Let `B_old=XT^2R` and `B_1=XT_1^2R`.  Telescoping gives

```text
rank(B_1-B_old)<=4,
rank(B_1^3-1)<=rank(B_old^3-1)+3 rank(B_1-B_old)<=18. (FNP2)
```

Round `B_1` to `B^3=1` and set `R_1=T_1^(-2)XB`, exactly as in the torsion
normalization proof.  Then

```text
rank(B-B_1)<=18,              rank(R_1-R)<=18.        (FNP3)
```

Since the original BS row is exact, telescoping its two `R` occurrences,
the one `T` occurrence, and the four occurrences in `T^4` yields

```text
rank(R_1T_1R_1^(-1)-T_1^4)
 <=18+2+18+4(2)=46.                                  (FNP4)
```

Multiplication by `T_1^(-4)` shows that the left side has the same rank as
`rho_p(v)-1`.

It remains to retain a discrete charge.  In every exact torsion frame,

```text
det(v)=det(T)^(-3)=det(XA)^(-3)=det(X),               (FNP5)
```

because `A^3=1` and `X^2=1`.  In the standard even Fourier model at
`p=1 mod 4`, the Fourier involution has trace one on the even subspace of
dimension `(p+1)/2`: both quadratic Gauss sums
`Tr(F)` and `Tr(FJ)` equal one.  Its negative eigenspace therefore has
dimension `(p-1)/4`.  For `p=5 mod 8` this is odd, so `det(X)=-1`.
Polar compression preserves this determinant by `(WCG7)`, and the torsion
normalization does not change `X`.  This proves the determinant assertion
in `(FNT1)`.

Finally, if a unitary `W` has `rank(W-1)<=r`, then

```text
|det(W)-1| <= sqrt(r)||W-1||_F.
```

With `W=rho_p(v)`, `(FNP4)` and `det(W)=-1` give
`||W-1||_F^2>=4/46=2/23`, proving `(FNT2)--(FNT3)`.  Frobenius squares and
ranks add under the blockwise normalization, proving `(FNT4)`.  Restoring
the deleted fixed line in every block is the exact even-Weil completion.
