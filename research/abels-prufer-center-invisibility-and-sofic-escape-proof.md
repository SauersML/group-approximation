---
rg: 2
id: abels-prufer-center-invisibility-and-sofic-escape-proof
kind: route
title: Quotient the top-right Abels root by its integer lattice and use Malcev on every finite-dimensional image
target: abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center
requires:
  - exact-fd-invisibility-has-no-general-hs-robustification
  - shared-center-pauli-tape-has-same-fp-gate
---

# The Abels Pruefer center is exact-invisible but sofic-visible

All matrix Hilbert--Schmidt norms below are normalized.

## 1. The finitely presented solvable parent

Fix a prime `p` and put `R=Z[1/p]`.  Consider the subgroup `A_p` of
`GL_4(R)` consisting of the matrices in (APQ3), with arbitrary
upper-triangular entries and middle diagonal entries in `p^Z`.

This is the positive-diagonal finite-index subgroup of the standard
four-by-four Abels group.  In the common indexing in which `Ab_n` is a
subgroup of the upper triangular matrices of size `n+1`, this is `Ab_3`
up to the finite diagonal sign group.  The Abels--Brown finiteness theorem
says that `Ab_n(Z[1/p])` is of type `F_(n-1)`.  Hence `Ab_3` is of type
`F_2`, equivalently finitely presented.  Finite-index subgroups of finitely
presented groups are finitely presented, so `A_p` is finitely presented.

The group is solvable because it is upper triangular.  In particular it is
amenable.

For `r in R` put `z(r)=I+rE_(1,4)`.  If `g in A_p`, then the first and last
diagonal entries of `g` are one and triangularity gives

~~~text
g E_(1,4)=E_(1,4)=E_(1,4) g.                             (1)
~~~

Therefore

~~~text
z(r)z(s)=z(r+s),             z(R)<=Z(A_p).               (2)
~~~

The map `r |-> z(r)` is injective, because its top-right matrix entry is
`r`.

## 2. The central quotient and its prime mark

Since `z(1)` is central, its normal closure is its cyclic subgroup:

~~~text
normal_closure_(A_p)(z(1))=<z(1)>=z(Z).                  (3)
~~~

Consequently the quotient

~~~text
Gamma_p=A_p/z(Z)                                         (4)
~~~

is obtained from a finite presentation of `A_p` by one additional relator.
It is finitely presented and remains solvable and amenable.

Equation (3) also shows that the image of `z(R)` in `Gamma_p` is exactly

~~~text
C=z(R)/z(Z) isomorphic_to Z[1/p]/Z.                       (5)
~~~

This is the Pruefer `p`-group `C_(p^infinity)`.  In particular

~~~text
c_p=z(1/p)z(Z) !=1,             c_p^p=1,                 (6)
~~~

and no smaller positive power is one.  The mark `c_p` is central and has
order exactly `p`.

For completeness, divisibility of (5) is elementary.  Given
`r+Z in Z[1/p]/Z` and an integer `N>=1`, write
`N=p^a q` with `gcd(p,q)=1`.  Division by `p^a` is available in `R`,
and multiplication by `q` is an automorphism of every finite cyclic
`p`-subgroup.  Thus there is `s+Z` with

~~~text
N(s+Z)=r+Z.                                               (7)
~~~

## 3. Every finite quotient kills the whole Pruefer center

Let `q:Gamma_p->F` be a homomorphism to a finite group, and take any
`c in C`.  Set `N=|F|`.  By (7), choose `b in C` with `b^N=c`.  Lagrange's
theorem gives

~~~text
q(c)=q(b)^N=1.                                            (8)
~~~

Thus every finite quotient of `Gamma_p` kills not just `c_p` but all of
`C`.

Now let `rho:Gamma_p->U(d)` be an exact finite-dimensional unitary
representation.  Its image `L=rho(Gamma_p)` is finitely generated because
`Gamma_p` is finitely generated.  It is a subgroup of `GL_d(C)`, so
Malcev's theorem says that `L` is residually finite.

If `rho(c_p)!=I`, residual finiteness of `L` supplies a finite quotient
`theta:L->F` with `theta(rho(c_p))!=1`.  The composite
`theta circ rho` contradicts (8).  Therefore

~~~text
rho(c_p)=I                                                (9)
~~~

for every exact finite-dimensional unitary representation.

Notice what is used here.  A Pruefer group certainly has faithful
one-dimensional unitary representations when considered by itself.  The
point is that the image of the entire finitely generated group `Gamma_p`
is a finitely generated linear group and is therefore residually finite.
The ambient finite generation is indispensable to the Malcev step.

## 4. Sofic microstates retain the mark maximally

Amenable groups are sofic, so `Gamma_p` has a faithful sofic approximation
`sigma_n:Gamma_p->Sym(D_n)`.  Since `c_p!=1`, it may be chosen with

~~~text
d_H(sigma_n(c_p),1)->1.                                  (10)
~~~

For a permutation `u` and its permutation matrix `P_u`,

~~~text
||P_u-I||_2^2
 =2-2 Re tr(P_u)
 =2(1-|Fix(u)|/|D_n|)
 =2 d_H(u,1).                                            (11)
~~~

Combining (10) and (11) proves

~~~text
||P_(sigma_n(c_p))-I||_2 -> sqrt(2).                     (12)
~~~

Thus (9) has no dimension-independent robustification from presentation
defect.  The relators can have defect tending to zero while the marked word
stays maximally separated.

## 5. A nonamenable calibration with a Kazhdan factor

Put

~~~text
Lambda_p=Gamma_p times SL_3(Z).                          (13)
~~~

Both factors are finitely presented and sofic, hence so is their direct
product.  The second factor is infinite, nonamenable and has property (T).
The element `(c_p,1)` is central.  Restricting any finite-dimensional
representation of `Lambda_p` to the first factor and applying (9) kills it,
whereas product sofic approximations retain it by (12).

This proves that nonamenability and a commuting Kazhdan sector do not repair
exact finite-dimensional invisibility.  It deliberately does not assert
that `Lambda_p` has property (T): projection onto the infinite amenable
factor `Gamma_p` rules that out.

## 6. Consequence for the shared-center Pauli route

The shared-center tape has substantially more structure than `Gamma_p`:
named Pauli pairs, tensor-site covariance and an actor action.  That extra
structure is exactly where a successful theorem would have to live.
The Abels example proves that the following shorter inference is false:

~~~text
finite presentation
+ central prime torsion
+ exact finite-dimensional invisibility
+ nonamenability or an auxiliary Kazhdan factor
=> normalized-HS invisibility.                            (14)
~~~

In particular, the exact identities

~~~text
D_-=2^m r
~~~

on every finite Pauli window cannot close the argument merely because the
whole tape has a finite presentation.  A matrix sequence may increase its
rank faster than every window reached at the current defect scale.  What is
still needed is one uniform theorem coupling the actor presentation to all
site names on a common positive-rank carrier.

## Sources

- H. Abels, *An example of a finitely presented solvable group*, in
  Homological Group Theory, LMS Lecture Note Series 36 (1979), 205--211.
- S. Witzel, *Abels's groups revisited*, arXiv:1206.0977, Example 1.1,
  records the type-`F_(n-1)` calculation and the four-by-four
  finite-presentation case.
- Y. de Cornulier, *On the isolated points in the space of groups*,
  arXiv:math/0511714, Section 5, records the Abels central quotient
  `Z[1/p]/Z isomorphic_to C_(p^infinity)`.
