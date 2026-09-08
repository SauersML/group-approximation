# A concrete two-track nonlinear feedback seed for Gottschalk

Date: 2026-09-08. This is an explicit candidate encoder and its exact
remaining decoder equations. Injectivity is not established, and no
missing output pattern is known. It is not a counterexample.

## Native encoder

Let a_1,b_1,a_2,b_2 be the four atlas generators of the binary
Leavitt unit group Q from binary-leavitt-unit-group-four-generated.
Each chart uses a=p_0 p_1 p_2 and b=p_3 p_5 p_4. Use the alphabet
F_2^2, with tracks X,Y. Define F on the whole full shift by

    F_1(X,Y)(g)
      = X(g)
        + X(g a_1)Y(g b_1) + X(g a_2)Y(g b_2),

    F_2(X,Y)(g)
      = Y(g)
        + X(g a_1^-1)Y(g b_1^-1)
        + X(g a_2^-1)Y(g b_2^-1).

All additions and products are Boolean operations over F_2.
The encoder has memory contained in the nine elements
1,a_1,b_1,a_2,b_2,a_1^-1,b_1^-1,a_2^-1,b_2^-1.
Both tracks are updated based on the data. No external certificate
track is supplied or fixed.

This passes elementary necessary tests:

* Every constant configuration is fixed: the two equal quadratic
  contributions in each output cancel.
* Each coordinate axis is fixed pointwise: F(X,0)=(X,0) and
  F(0,Y)=(0,Y).
* F fixes every one-particle input.
* F creates particles on a two-particle input. Put X(a_1)=1,
  Y(b_1)=1, and all other input bits zero. F_1(1)=1, because
  the second pair uses different native generators. The original
  X-particle at a_1 is unchanged: a quadratic contribution there
  would require some a_i=1. The original Y-particle at b_1 is
  unchanged for the same reason with b_i. Thus the output has at
  least three particles. Further creations do not spoil this fact.

The particle statement uses distinctness and nontriviality of the
native generators, which are also authenticated by the first
collision audit. It does not establish injectivity. Axis invariance
is not preservation of one certificate track on all configurations.

## Every local decoder has a constrained nonlinear form

If D F=id, then D(0)=0. Because F fixes the whole X-axis and Y-axis,
D must fix those axes pointwise as well. In Boolean algebraic normal
form, every nonlinear monomial of D therefore involves both tracks.
In particular its linear part is exactly the identity.

Consequently a quadratic decoder, if one exists, necessarily has

    D_1(X,Y)(g) = X(g) + sum_(s,t) d_1(s,t)X(gs)Y(gt),
    D_2(X,Y)(g) = Y(g) + sum_(s,t) d_2(s,t)X(gs)Y(gt),

where the coefficients are in F_2 and only finitely many are nonzero.
Allow s=t: the two variables are still on distinct tracks.
No linear terms, constants, or same-track quadratic terms have
been omitted from this quadratic decoder ansatz.

## The exact construction equations

Write

    B={(a_1,b_1),(a_2,b_2)},
    C={(a_1^-1,b_1^-1),(a_2^-1,b_2^-1)},

and let

    P(X,Y)=sum_((a,b) in B) X_a Y_b,
    Q(X,Y)=sum_((c,d) in C) X_c Y_d.

For a finitely supported coefficient array z(s,t), define

    L(z) = sum_(s,t) z(s,t)
        (X_s + sum_((a,b) in B) X_(sa)Y_(sb))
        (Y_t + sum_((c,d) in C) X_(tc)Y_(td)).

These are polynomials in the actual Q-indexed Boolean variables,
with the exact relations X_h^2=X_h and Y_h^2=Y_h. The left-inverse
conditions are precisely

    L(d_1)=P,                 L(d_2)=Q.                 (1)

For any fixed decoder memories these are LINEAR equations over F_2
in d_1,d_2. The nonlinear encoder has already been specified.
To obtain the equations, expand each summand as

    X_sY_t
    + sum_C X_s X_(tc) Y_(td)
    + sum_B X_(sa) Y_(sb) Y_t
    + sum_(B,C) X_(sa) X_(tc) Y_(sb) Y_(td),             (2)

reduce repeated variables using Boolean idempotence and actual group
equalities, and match every squarefree coefficient through degree
four. This is literal function composition, not a derivative,
secant inverse, or linearization around a certificate.

A solution of (1) must then be checked for a reverse defect

    P(D_1,D_2)+sum_(s,t)d_1(s,t)X_sY_t != 0

or

    Q(D_1,D_2)+sum_(s,t)d_2(s,t)X_sY_t != 0.             (3)

These are exactly F D-id in the two tracks, again evaluated after
shifts and Boolean reduction. If both vanish, the rule is reversible
and does not answer Gottschalk.

If one reverse polynomial is nonzero, choose an inclusion-minimal
set of its variables with nonzero squarefree coefficient, set those
variables to one, and set the other variables to zero. This produces
a finite output configuration y with F D(y)!=y. Under (1), y is
outside the image of F. Thus (1) plus a nonzero residual in (3)
would be a complete finite-alphabet counterexample with a literal
local decoder and an explicit missing finite pattern.

## Why native mixed group identities must enter the equations

The completed MSI audits excluded two earlier address-only seeds:

* M={1,a_1,b_1,a_2,b_2}, S=M^-1: both composition rectangles
  lift to A8*A8.
* Adjoining B_0=[q13(f),q32(f*)] to M and
  A_0=[q13(e),q32(e*)], C_0=[q13(1),q32(1)] to S:
  both rectangles lift to (A8*A8)*V4 with fresh A_0,B_0 and
  C_0=A_0 B_0.

The actual Leavitt relation A_0 B_0=C_0 is present in the second
table, but its commutator dictionary is not forced there. Therefore
neither seed allows a strict CA over any finite alphabet.

For the feedback encoder above, increasing decoder memory can
introduce genuine identities among sa,sb,tc,td in (2), including
the mixed ring relations. A solution over a rectangle that still
lifts to a surjunctive source cannot be strict. Prefix addresses must
authenticate any purported mixed relation; naming a complicated
Leavitt word as one fresh address does not suffice.

The present unsolved task is therefore exact and constructive:
find finite supports for d_1,d_2 solving (1), and exhibit a nonzero
reverse polynomial (3), or prove this particular encoder has an
explicit collision. Neither outcome has been established.
No computation of (1) has been run in this pass.

