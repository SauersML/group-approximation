---
rg: 2
id: tfd-compression-flexible-reduction-proof
kind: route
title: Round the compression projection in the finite-dimensional commutant
target: tfd-low-leakage-compressions-flexibly-reduce
requires: []
---

Write `U_s=pi(s)` and let `N=pi(Gamma)'`.  The conjugation action of
`Gamma` on the finite-dimensional Hilbert space `M_(dim H)`, with
unnormalized Frobenius norm, has fixed space `N`.  Property `(T;FD)`
applies because this conjugation representation is finite-dimensional.  If
`A=E_N(P)` is the orthogonal conditional expectation of `P` onto `N`,
then

```text
||P-A||_F
 <= kappa^(-1) max_(s in S)||[P,U_s]||_F
 <= (sqrt(2)/kappa) sqrt(L(P,pi)).                       (1)
```

For the last inequality, the two off-diagonal corners of a unitary have the
same Frobenius norm, so

```text
||[P,U_s]||_F^2
 =2||(1-P)U_sP||_F^2.                                   (2)
```

The operator `A` is a positive contraction in `N`.  Set

```text
Q=1_[1/2,1](A).
```

Then `Q in N`.  Trace preservation and bimodularity of `E_N` give

```text
||P-A||_F^2
 =Tr(P)-Tr(A^2)
 =Tr(A-A^2).                                            (3)
```

For `0<=t<=1` and `q(t)=1_[1/2,1](t)`,

```text
|t-q(t)|^2<=t(1-t).
```

Functional calculus and `(3)` imply
`||A-Q||_F<=||P-A||_F`.  Moreover `P-A` is orthogonal to `N`, whereas
`A-Q` lies in `N`.  Therefore

```text
||P-Q||_F^2
 =||P-A||_F^2+||A-Q||_F^2
 <=2||P-A||_F^2
 <=(4/kappa^2)L(P,pi).                                  (4)
```

For any two finite-rank projections,

```text
|rank(P)-rank(Q)|<=||P-Q||_F^2.                         (5)
```

Equations `(4)--(5)` prove `(TLC2)` and `(TLC4)`.

It remains to compare the compressed generators.  Let
`B_s=P U_s P` on `PH`, and let `rho(s)` be a unitary polar completion
of `B_s`.  If `t_i` are the singular values of `B_s`, then

```text
||rho(s)-B_s||_F^2
 =sum_i(1-t_i)^2
 <=sum_i(1-t_i^2)
 =||(1-P)U_sP||_F^2.                                    (6)
```

Extend both corner operators by zero on the orthogonal complements in
`H`.  Since `Q` reduces every `U_s`,

```text
||P rho(s) P-Q U_s Q||_F
 <=||(1-P)U_sP||_F+2||P-Q||_F.                          (7)
```

The standard principal-angle matching for `P,Q` now identifies subspaces
of common dimension

```text
d-O(||P-Q||_F^2)
```

and has squared Frobenius displacement `O(||P-Q||_F^2)`.  On the unmatched
part, add arbitrary trivial exact summands; by `(5)` this part has
dimension `O(L(P,pi))`.  Divide `(7)` by `sqrt(d)`, sum over the fixed
finite set `S`, and use `(4)`.  The matched generator error and the
square root of the unmatched dimension fraction are both
`O_kappa(sqrt(L(P,pi)/d))`.  This is precisely the almost-full-isometry
description of Dogon--Vigdorovich's generalized Hilbert--Schmidt metric and
proves `(TLC3)`.

For `SL_2(Z[1/2])`, the required uniform finite-dimensional constant is
the property-`(T;FD)` constant already used in the strict even-Weil
intertwiner argument.  The proof uses no bound on `dim(H)-d`; only the
actual generator leakage in `(TLC1)` matters.
