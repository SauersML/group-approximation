---
rg: 2
id: two-port-magic-square-holonomy-proof
kind: route
title: Eliminate a transverse two-port square and classify its port image
target: two-port-magic-square-commutator-is-holonomy-square
requires:
  - row-glued-magic-squares-absorb-noncommuting-ports
---

# Eliminate a transverse two-port square and classify its port image

## Setup

Let the nine cell observables be involutions, and suppose observables in each
row and each column commute.  Abbreviate

``
\begin{array}{ccc}
a&b&p\\
c&d&f\\
g&h&i
\end{array}
=
\begin{array}{ccc}
x_{11}&x_{12}&x_{13}\\
x_{21}&x_{22}&x_{23}\\
x_{31}&x_{32}&x_{33}.
\end{array}
``

Fix signs `A,B,C,D\in\{\pm1\}` and impose

``
R_1=Z,\quad R_2=A I,\quad R_3=B I,
\qquad
C_1=W,\quad C_2=C I,\quad C_3=D I.
``

Put `\kappa=ABCD`.  The port observables `Z` and `W` are involutions because
they are products of commuting involutions on their respective lines.

## 1. Exact elimination

The four scalar equations give, in order,

``
f=Acd,qquad h=Cbd,qquad
i=Bgh=BCgbd,qquad
p=Dfi=\kappa cdgbd.
``

The third row says `g` commutes with `h=Cbd`.  Since `b` commutes with `d`,

``
cdgbd=cdbdg=cbg,
``

and consequently

``
p=\kappa cbg.                                           \tag{1}
``

The third-column commutation `[f,i]=1` loses the scalar factors and says

``
(cd)(gbd)=(gbd)(cd).
``

Simplifying the left side as above and using
`[b,d]=[c,d]=1` on the right gives

``
cbg=gbc.                                                  \tag{2}
``

The first-row commutation `[b,p]=1` and (1) give

``
bcbg=cbgb.                                                \tag{3}
``

Right-multiply (2) by `c` and use `[c,g]=1`:

``
gb=cbcg.                                                  \tag{4}
``

Substituting (4) into the right side of (3), then cancelling `g`, yields

``
bcb=cbcbc.
``

After right multiplication by `b` this becomes

``
bc=(cb)^3=(bc)^{-3},
``

so

``
\boxed{(bc)^4=1.}                                       \tag{5}
``

Now (1) gives

``
Z=abp=\kappa abcbg,
\qquad
W=acg.
``

The element `a` commutes separately with `b,c,g`, and `c` commutes with `g`.
Therefore

``
ZW
=\kappa abcbgacg
=\kappa bcb c
=\kappa(bc)^2.                                          \tag{6}
``

Equations (5)--(6) imply `(ZW)^2=1`.  Since `Z` and `W` are involutions,

``
\boxed{ZW=WZ.}                                          \tag{7}
``

Thus the transverse cell forces commutativity in every representation, not
only in Pauli or class-two representations.

## 2. The ordering holonomy has no remaining escape

Let

``
P_R=R_1R_2R_3,qquad P_C=C_1C_2C_3,qquad
\Omega=P_C^{-1}P_R.
``

The row-major and column-major words contain each cell once, so
`\Omega` lies in the derived subgroup of the cell-generated group.  After
the line equations are imposed,

``
\Omega=(WCD)^{-1}(ZAB)=\kappa WZ.
``

By (6)--(7),

``
\boxed{\Omega=(bc)^2,\qquad \Omega^2=[W,Z]=1.}        \tag{8}
``

The holonomy identity is therefore not a channel through which a general
source commutator can pass: the rest of the same square makes that holonomy
an involution.

## 3. Every commuting pair extends

The necessary condition (7) is sharp.  Suppose `Z` and `W` commute on a
Hilbert space `H`.  Their joint spectral projections are

``
P_{z,w}=\frac14(I+zZ)(I+wW),
\qquad z,w\in\{\pm1\}.
``

On the `(z,w)` sector, prescribe the six scalar line signs

``
(r_1,r_2,r_3;c_1,c_2,c_3)=(z,A,B;w,C,D).                \tag{9}
``

Their total parity is `zw\kappa`.

For every profile of total parity `+1` there is a scalar square.  One explicit
construction sets the upper-left `2\times2` cells to `1`, then sets

``
y_{13}=r_1,quad y_{23}=r_2,quad
y_{31}=c_1,quad y_{32}=c_2,quad
y_{33}=r_3c_1c_2.
``

The final column has product `c_3` exactly because
`r_1r_2r_3c_1c_2c_3=1`.

For total parity `-1`, start with the two-qubit Mermin--Peres square

``
\begin{array}{ccc}
I\otimes X&X\otimes I&X\otimes X\\
Z_0\otimes I&I\otimes Z_0&Z_0\otimes Z_0\\
Z_0\otimes X&X\otimes Z_0&Y\otimes Y
\end{array}
``

whose row signs are `(+,+,+)` and column signs are `(+,+,-)`.
The ratio of any other odd profile to this one has even total parity, hence
is realized by a scalar cell-sign square from the preceding paragraph.
Multiplying the Pauli cells by those signs realizes the desired odd profile
on `\mathbb C^4`.

Let `X_{ij}^{z,w}` be a four-dimensional realization of (9), taking four
copies of a scalar square in the even case.  Define

``
\widehat X_{ij}
=\sum_{z,w}P_{z,w}\otimes X_{ij}^{z,w}
\quad\hbox{on }H\otimes\mathbb C^4.
``

Orthogonality of the joint spectral projections shows that these are
involutions, that every row and column commutes, and that the four scalar
line products are `A,B,C,D`.  Moreover,

``
\widehat R_1
=\sum_{z,w}zP_{z,w}\otimes I
=Z\otimes I,
\qquad
\widehat C_1
=\sum_{z,w}wP_{z,w}\otimes I
=W\otimes I.
``

Therefore a pair of involutions extends through this cell, after amplification
by at most four, if and only if it commutes.

## 4. Dimension-free robust bound

Assume now that cell involutions and all within-line commutations remain exact,
but the six displayed line equations have normalized Hilbert--Schmidt defects
`\eta_{R_i},\eta_{C_j}`.  The following bookkeeping makes the constant
explicit.

The second row, second column, third row, and third column first give

``
\begin{aligned}
\|f-Acd\|_2&\leq\eta_{R_2},\\
\|h-Cbd\|_2&\leq\eta_{C_2},\\
\|i-BCgbd\|_2&\leq\eta_{R_3}+\eta_{C_2}.
\end{aligned}
``

Because `g` commutes with `h`,

``
\|gbd-bdg\|_2\leq2\eta_{C_2}.
``

Substitution into the third column and one use of this last estimate give

``
\|p-\kappa cbg\|_2\leq E_p,
\qquad
E_p=\eta_{C_3}+\eta_{R_2}+\eta_{R_3}+3\eta_{C_2}.    \tag{10}
``

Exact commutation of `f` and `i`, followed by the same substitutions, gives

``
\|cbg-gbc\|_2\leq E_C,
\qquad
E_C=2\eta_{R_2}+2\eta_{R_3}+4\eta_{C_2}.             \tag{11}
``

Exact commutation of `b` and `p` and (10) give

``
\|bcbg-cbgb\|_2\leq2E_p.                             \tag{12}
``

Repeating the exact derivation (4)--(5) with (11)--(12), using bi-invariance
at each multiplication, yields

``
\|(bc)^4-I\|_2\leq2E_p+E_C.                          \tag{13}
``

If `R_1=abp` and `C_1=acg` denote the actual first-line words, then (10) and
the exact simplification in (6) show

``
\|R_1C_1-\kappa(bc)^2\|_2\leq E_p.
``

Both line words are involutions.  Hence, by
`\|U^2-V^2\|_2\leq2\|U-V\|_2`,

``
\|[R_1,C_1]-I\|_2
\leq4E_p+E_C
\leq16(\eta_{R_2}+\eta_{R_3}+\eta_{C_2}+\eta_{C_3}).
``

Finally replacing `R_1,C_1` by the target ports `Z,W` costs at most
`2\eta_{R_1}+2\eta_{C_1}`.  Therefore

``
\boxed{
\|[Z,W]-I\|_2
\leq16\left(\sum_i\eta_{R_i}+\sum_j\eta_{C_j}\right).
}                                                        \tag{14}
``

The constant is deliberately not optimized.  What matters for the compiler
search is that it is absolute and dimension independent.

## 5. Frontier consequence

The minimal transverse two-port square is completely classified:

- one port is a universal four-dimensional absorber;
- two ports on alignable separate squares are still universally absorbed;
- two transverse ports on one square are exactly a robust commutativity
  quotient.

Thus neither placement supplies a finite-versus-commuting separation.  A live
cyclic gadget must have more than one irreducible cell cycle and an induced
port relation already satisfied by the desired commuting-operator source
model, while retaining a reverse estimate that rules out the finite-dimensional
escape.
