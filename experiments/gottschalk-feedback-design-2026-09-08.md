# Nonlinear feedback attempts and exact exclusions

Date: 2026-09-08. The two-track encoder below is now excluded by the
factorization proof at the end of this note. Its exact equations are
retained to document the construction attempt. The subsequent four-track
encoder has an explicit finite-support collision. Its alternating
bilinear replacement is also excluded under injectivity, by the
factorization below. No counterexample is constructed.

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

No computation of (1) has been run in this pass. The pure mathematical
argument below now proves that a solution of (1) cannot have a strict
reverse defect; searching this two-track architecture is unnecessary.

## Why the two-track architecture cannot be strict

More generally suppose F(X,Y)=(L_Y X,V(X,Y)), where L_Y is linear
in X for fixed Y, and F fixes both coordinate axes. If F is injective,
each L_Y is injective: L_Y X=0 would give F(X,Y)=(0,Y'), which
also equals F(0,Y'). Thus E(X,Y)=(L_Y X,Y) is an injective CA.
Its Y=0 fiber is the identity. The established certificate-fiber
theorem therefore makes E bijective with a local inverse.

Now F composed with E^-1 preserves its first track. Its fiber at
first track zero is again the identity. The same certificate-fiber
theorem makes this injective composition surjective. Hence F itself
is surjective whenever it is injective.

Pure three-track cyclic bilinear feedback also reduces to this case.
For F=(X+P(Y,Z),Y+Q(Z,X),Z+R(X,Y)), make the reversible input
substitution X_old=X+P(Y,Z). The first output is X. Its X=0 fiber
is

    (Y+Q(Z,P(Y,Z)), Z+R(P(Y,Z),Y)).

This fixes both axes and is homogeneous linear in Y in its first
coordinate for each fixed Z. The preceding argument makes that fiber
bijective under injectivity. The preserved-X fiber theorem then
makes the entire map bijective. This independently checks the root
agent's elimination argument.

## Four-track cyclic feedback with repeated dependence

Define one native bilinear operation

    B(U,V)(g)=U(ga_1)V(gb_1)+U(ga_2)V(gb_2).

On alphabet F_2^4 take the explicit encoder

    F_i=X_i+B(X_(i+1),X_(i+2)),       indices modulo four.

All constants and coordinate axes are fixed. A pair of particles on
the two control tracks creates a particle on a third track. Every
track is updated on some configuration.

Eliminate the first two output coordinates using reversible input
shears. At their zero fiber write the two remaining inputs as z,w.
The old inputs are then

    X_2=B(z,w),       X_1=B(B(z,w),z),

and the remaining output map is

    H(z,w)=(z+B(w,B(B(z,w),z)),
            w+B(B(B(z,w),z),B(z,w))).

The two nonlinear terms have bidegrees (2,2) and (3,2) in (z,w)
before Boolean reduction. Both variables repeat. Thus the two-track
conditional-linearity proof above does not apply to this residual
map. This is an identified limitation of that proof, not evidence
that the encoder is injective or strict.

For chosen finite decoder memories, literal Boolean composition
still supplies exact coefficient equations. A quadratic decoder
for a fixed quadratic encoder can be solved for linearly in its
coefficients; a higher-degree decoder has the same linearity in
its unknown coefficients, with larger observable monomials. A
nonzero reverse residual is still required for a counterexample.

This encoder is now proved noninjective. With K_1 the first finite
GL_4(F_2) chart subgroup and Z=1_(K_1), one has B(Z,Z)=Z and hence
F(Z,Z,Z,Z)=0=F(0,0,0,0). The first summand of B gives Z, while
the second vanishes because a_2^-1 b_2 is outside K_1. The independent
chart-separation calculation and exact finite collision are recorded
in `research/artifacts/gottschalk-four-track-finite-chart-collision-2026-09-08.md`.
No decoder search for this encoder is warranted.

## Alternating bilinear replacement: injectivity forces bijectivity

The tempting repair is to alternate B so B(U,U)=0 identically. This
eliminates the preceding all-track mask collision. For example use

    B(U,V)=U_a1 V_b1+U_b1 V_a1+U_a2 V_b2+U_b2 V_a2.

Nevertheless every alternating bilinear B on binary configurations
gives a four-cycle F_i=X_i+B(X_(i+1),X_(i+2)) which is surjective
whenever it is injective. This statement concerns the same B in all
four coordinates; it makes no claim about arbitrary nonlinear rules
or different bilinear operations in different coordinates.

Here is a direct proof. Alternation implies B(U,V)=B(V,U). If
B(U,W)=U with U nonzero, then

    F(U+W,W,U,U)=F(W,W,0,0)=(W,W,0,0).

Consequently injectivity of F forces L_W(U)=U+B(U,W) to be injective
for every W. The CA E(U,W)=(L_W(U),W) is then injective and has the
identity fiber at W=0. Apply
`nonlinear-certificate-fibers-are-all-surjective-or-all-strict`:
E is bijective and its inverse is a CA. In particular the assignment
(Y,W) to L_W^-1(Y) is local.

Use invertible track coordinates

    r=X_1+X_2+X_3+X_4,       p=X_1+X_3,
    z=X_1+X_2,               x=X_1.

The first output coordinate is

    r'=r+B(p,r)=L_p(r).

The reversible input change r_old=L_p^-1(r) makes r the preserved
output coordinate. On its zero fiber r_old=0 and the remaining
output coordinates, before a further input change, are

    p'=p+B(p,z)=L_z(p),
    z'=z+B(x,p),
    x'=x+B(x,p)+B(z,p)+B(x,z).

Now make the reversible input change p_old=L_z^-1(p) within this
fiber. The output preserves p. On p=0 the last two coordinates are

    (z',x')=(z,x+B(x,z)),

which is bijective by the already established inverse of E. The
certificate-fiber theorem first makes the entire r=0 fiber
bijective, then makes the full r-preserving map bijective. Undoing
the reversible coordinate changes proves F is bijective.

Both exceptional repairs considered here are therefore resolved:
the native two-chart B has an explicit collision; alternating B
throughout this four-cycle cannot give a strict injective map.
