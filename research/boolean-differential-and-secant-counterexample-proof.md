---
rg: 2
id: boolean-differential-and-secant-counterexample-proof
kind: route
title: Differentiate the Boolean relation and compute the three secant columns of a reversible gate
target: boolean-secants-do-not-supply-operator-left-inverses
requires: []
---

## Ordinary derivatives do not descend to Boolean functions

Every element of R depends on finitely many variables, and the usual
Boolean relations reduce it to a multilinear polynomial. In the module
of Kahler differentials, each defining relation gives

    0=d(x_i^2-x_i)=(2x_i-1)dx_i=dx_i.

The dx_i generate the differential module, hence Omega_(R/F_2)=0.
For a particularly direct illustration, x and x^2 represent the same
function on F_2; their polynomial derivatives are 1 and 0 respectively.
Even the identity permutation, represented by x^2 and decoded by x,
has functional composition equal to x but formal derivative zero for
that composition. Functional inversion alone therefore cannot justify
the usual Jacobian inverse equation for chosen polynomial representatives.

## The telescoping construction is intrinsic but weaker

For a function F:F_2^m->F_2^n and x,y in F_2^m, put

    p_i=(y_1,...,y_i,x_(i+1),...,x_m),    i=0,...,m.

Define column i of D_F(x,y) to be the Boolean difference of F in its
i-th argument, holding preceding arguments at their y-values and later
arguments at their x-values. This definition makes sense even if x_i=y_i:
evaluate that argument at 1 and 0 and add the results. Then

    F(p_i)+F(p_(i-1)) = (y_i+x_i) column_i(D_F(x,y)).

Summing the finite telescope gives

    F(y)+F(x)=D_F(x,y)(y+x).                         (BSC1)

For a decoder E with E F=id, apply (BSC1) to E at F(x),F(y):

    y+x = D_E(F(x),F(y)) D_F(x,y)(y+x).              (BSC2)

This proves an equality on the particular vector y+x. It gives no
equality on other vectors while the pair (x,y) is held fixed.

## A reversible gate with a singular secant

Take t=b(1+a+c) and F(a,b,c)=(a+t,b,c+t). The gate preserves b and a+c,
so it preserves t as well. Applying it twice adds t twice to a and c,
hence F^2=id. On binary inputs it swaps 010 with 111 and fixes the other
six triples.

For x=000, y=111 the ordered interpolation path and its images are

    p_0=000 -> F(p_0)=000,
    p_1=100 -> F(p_1)=100,
    p_2=110 -> F(p_2)=110,
    p_3=111 -> F(p_3)=010.

All three coordinate differences y_i+x_i equal 1. The secant columns are
therefore the successive image differences 100,010,100, exactly the
matrix in the claim. Its rank is two and its kernel contains 101.
Nevertheless its value on the actual disagreement 111 is 010, as (BSC1)
requires. Since any product with this singular matrix has rank at most
two, (BSC2) cannot be upgraded to a 3-by-3 identity matrix in this example.

Applying F independently at every group coordinate gives a reversible
cellular automaton with no spatial memory. For the constant pair of
certificates x(g)=000, y(g)=111, the associated secant-linear automaton
kills a data vector equal to 101 at one site and zero elsewhere. Thus
the loss of injectivity survives verbatim in the full-shift setting.

The genuine certificate-linear compiler requires a family that is
injective on all data for each certificate. Restricting the input data
to the single disagreement determined by that certificate supplies
strictly less information, as the displayed reversible example proves.

## Minimality and a different finite-space construction

Every permutation of F_2 is affine. For a permutation F of F_2^2, subtract
F(0). Its values at the two standard basis vectors are distinct nonzero
vectors and hence form a basis. Its value at their sum must be the
remaining nonzero vector, which is the sum of those two images. Thus F
is affine as well. An affine map F(v)=Av+b has D_F(x,y)=A for every pair,
so no one- or two-bit permutation has a singular telescoping secant.

To see concretely why this does not exclude other secant choices, fix a
dimension m>=1. For each nonzero h in F_2^m choose U_h in GL_m(F_2) with
U_h e_1=h. For a permutation F define

    L_F(x,y)=U_(F(y)+F(x)) U_(y+x)^(-1),  if x!=y,
    L_F(x,x)=I.

Then L_F(x,y) is invertible and sends y+x to F(y)+F(x). Using the same
frames for every permutation gives the exact composition rule

    L_(E F)(x,y)=L_E(F(x),F(y)) L_F(x,y).

For unequal inputs this follows by cancellation of the intermediate
frame; for equal inputs all three matrices are I. In particular the
secant of F^(-1) is the operator inverse of the secant of F at the
corresponding pair. This construction also works sitewise for a fixed
finite reversible gate, because its table is finite.

For a cellular automaton on an infinite group, however, disagreements
are entire configurations. This argument neither chooses local frames
for them nor provides a uniform finite memory for the resulting
operators. It therefore repairs the finite-gate example without proving
the local nonlinear-to-linear compiler that the open route would need.
