---
rg: 2
id: certificate-linear-decoder-clopen-patching-proof
kind: route
title: Extend finite-coordinate inverse functionals and patch their certificate cylinders
target: certificate-linear-automata-have-local-linear-decoders
requires: []
---

## A finite linear formula at each certificate

Write X=B^G with the left shift (h.c)(g)=c(h^(-1)g). After taking a common
finite memory F, the data rule can be written

    (T_c x)(g)=sum_(s in F) a_s(g^(-1).c) x(gs),

where a_s:X->M_n(k) are locally constant. A locally constant function on
this compact product depends on finitely many certificate coordinates.

Since E keeps its certificate, injectivity of E is exactly injectivity of
every T_c. Fix c. The continuous injection T_c from the compact Hausdorff
space (k^n)^G is a homeomorphism onto its image. The map that recovers
x(1) from T_c x is continuous on that image. Because k^n is finite, it
depends on only finitely many output coordinates, say H_c subset G.
For completeness, cover the image by finitely many cylinder neighborhoods
on each of which the recovered value is constant, and take the union of
their coordinate sets.

Define U_c={(T_c x)|_(H_c):x in (k^n)^G}, a linear subspace of
(k^n)^(H_c). The assignment (T_c x)|_(H_c) -> x(1) is well-defined by
the preceding finite dependence, and linear because T_c is linear.
Extend this map to a linear map on the whole finite-dimensional space
(k^n)^(H_c). Thus there are matrices b_(c,h) with

    sum_(h in H_c) b_(c,h) (T_c x)(h)=x(1) for every x.       (CLD1)

No assertion is made that an arbitrary nonlinear extension of the inverse
would be linear; the finite-dimensional extension is chosen to be linear.

## The same formula works on a certificate neighborhood

Substituting the finite local rule for T into (CLD1) involves only
a_s(h^(-1).c), for h in H_c and s in F. These depend on finitely many
coordinates of c. Fixing those coordinates gives a clopen neighborhood
V_c on which exactly the same matrices b_(c,h) satisfy (CLD1).
Group multiplication coincidences among the finitely many hs do not
depend on c, so they cause no additional condition when c changes.

The neighborhoods V_c cover the compact space X. Choose a finite subcover
V_1,...,V_m and refine it to a disjoint clopen partition, for example by
successively removing earlier V_i. On each nonempty part choose the
formula attached to its V_i. With H the union of the finitely many H_i,
padding missing coefficients by zero yields locally constant functions
b_h:X->M_n(k) satisfying

    sum_(h in H) b_h(c) (T_c x)(h)=x(1) for all c,x.

## Shift the origin formula to every cell

Set

    (S_c y)(g)=sum_(h in H) b_h(g^(-1).c) y(gh).

This has finite certificate and data memory. Applying the origin identity
to g^(-1).c and the data configuration z(h)=x(gh), and using equivariance
of T, gives (S_c T_c x)(g)=x(g). Therefore D E=id on the full shift.
This proves the claimed local linear decoder, including on every malformed
certificate. It supplies no identity T_c S_c=I.
