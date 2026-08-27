---
rg: 2
id: even-weil-second-cubic-has-a-rank-six-determinant-gap
kind: claim
title: The compressed even-Weil second cubic has a rank-six determinant gap at primes five modulo eight
distinct_from:
  even-weil-fixed-line-compression: that proves the rank-one compression upper bound and strict nonextension; this computes a matching lower bound for one particular cubic word on an infinite prime subsequence.
  iwahori-cycle-packet-determinant-fence: that uses determinant only as an exact packet classifier and notes its general HS dilution; this combines determinant with a uniform rank bound on the compressed cubic residual, converting it into normalized-HS soundness.
  bs14-two-cubic-strict-repair-constants-diverge: that needs only the cubic upper bound and strict separation; this closes the missing lower-bound calibration and determines the exact defect scale on the five-modulo-eight family.
---

Let `p=5 mod 8` be prime.  In the even Schrodinger--Weil representation of
`PSL_2(F_p)`, let `q=delta_0`, `P=1-q`, and let `(X_p,R_p,S_p)` be the
polar-rounded compression to `P H` from
`even-weil-fixed-line-compression`.  Put `d=(p-1)/2` and

```text
W_p=(X_p R_p S_p)^3.                                  (WCG1)
```

Then

```text
rank(W_p-1)<=6,             det(W_p)=-1,               (WCG2)
||W_p-1||_(2,d) >= 2/sqrt(6d).                         (WCG3)
```

In particular, together with the known compression upper bound,

```text
max(||(X_p S_p^2)^3-1||_2,||(X_p R_p S_p)^3-1||_2)
  =Theta(p^(-1/2))                                      (WCG4)
```

on the infinite prime progression `p=5 mod 8`.

## Determinant calculation

Use the standard Schrodinger normalization.  Since `p=1 mod 4`, the Weyl
involution is the selfadjoint Fourier transform and

```text
<q,Xq>=p^(-1/2)>0.                                    (WCG5)
```

Put `A=PXP` and `X_p=sgn(A)`.  If
`v=P X q/sqrt(1-p^(-1))`, then on `span(q,v)` the full involution has matrix

```text
[[a,sqrt(1-a^2)],[sqrt(1-a^2),-a]],   a=p^(-1/2),     (WCG6)
```

of determinant `-1`, while `X_p v=-v`; off this plane `X_p` and `X` agree.
Therefore

```text
det(X_p)=det(X).                                      (WCG7)
```

The half-parabolic fixes `q`, so `S q=q`.  The diagonal Weil implementer
acts on `q` by the quadratic character,

```text
R q=(2|p)q=-q                                         (WCG8)
```

because `p=5 mod 8`.  The full second cubic is exact.  Taking determinants
and removing the `q` eigenvalues gives

```text
det(W_p)
 =[det(X_p) det(R|_(PH)) det(S|_(PH))]^3
 =[det(X) det(R) det(S)]^3 (2|p)^(-3)
 =-1.                                                 (WCG9)
```

## Rank and norm calculation

Let `Y=XRS` on the full even Weil space and `B=PYP=A(R|_(PH))(S|_(PH))`.
Since `Y^3=1`, insert `P+q` in the two internal slots of `P Y^3 P`.
Besides `B^3`, the three remaining terms each factor through the
one-dimensional space `qH`.  Hence

```text
rank(B^3-P)<=3.                                       (WCG10)
```

The difference `X_p-A` has rank one.  Telescoping the cubes of
`X_p(RS)|_(PH)` and `A(RS)|_(PH)` writes their difference as three rank-one
terms, so

```text
rank(W_p-B^3)<=3,                                     (WCG11)
```

proving the rank bound in `(WCG2)`.

Finally, if a unitary `U` has `rank(U-1)<=r`, telescope its nontrivial
eigenvalues to get

```text
|det(U)-1| <= sum_j |lambda_j-1|
             <= sqrt(r)||U-1||_F.                     (WCG12)
```

Apply `(WCG12)` with `det(W_p)=-1` and `r=6`, then divide the Frobenius norm
by `sqrt(d)`.  This proves `(WCG3)`.

## Padding calibration

The full even Weil representation adds exactly the deleted line and is an
exact extension in dimension `d+1`, at generalized HS distance
`O(p^(-1/2))`.  Property `(T;FD)` gives a fixed lower distance from every
exact extension in dimension `d`.  Therefore, among exact representations
asymptotically close to this compressed family, the minimum number of added
dimensions is exactly one: zero cannot work and one does.  Since

```text
1/(d+1)=2/(p+1)=Theta(||W_p-1||_2^2),                 (WCG13)
```

the quadratic flexible-padding scale is genuinely sharp on this subsequence.
