---
rg: 2
id: qutrit-cycle-phase-flip-finite-amalgam-proof
kind: route
title: Compute the four translated phase rows and build the virtually free flip cover
target: qutrit-first-cycle-phase-flip-is-a-finite-amalgam
requires:
  - qutrit-first-directed-cuntz-cycle-is-full-leavitt-rank-four
  - qutrit-central-line-twist-is-impossible-in-jacobson-host
---

## The four root rows

Use the cyclic order

```text
c_0=i, c_1=j, c_2=ell, c_3=k.
```

Conjugation by `P` increases every subscript by one modulo four. Starting
from the row in the directed-cycle theorem gives

```text
X_(a,s)=P^a X_(0,s)P^(-a)=x_(c_(a+2),c_a)(t_s),
Y_(a,r)=P^a Y_(0,r)P^(-a)=x_(c_a,c_(a+1))(s_r),
D_a    =P^a D_0P^(-a)    =x_(c_(a+2),c_(a+1))(1).
                                                               (QPF5)
```

The first two roots are composable, and the Steinberg commutator is

```text
[X_(a,s),Y_(a,r)]
 =x_(c_(a+2),c_(a+1))(t_ss_r)
 =D_a^(delta_(sr)).                                      (QPF6)
```

This proves the algebraic part of every row without a completion or a
representation.

## Character support and exact masses

All four coordinates are fixed by `h=J^2Z`. Their `C=<J,Z>` types in
cyclic order are

```text
triv, nontriv, nontriv, triv.                            (QPF7)
```

The two endpoints of `X_(a,s)` are opposite on this cycle and therefore
always have different type. The endpoints of `Y_(a,r)` have different
type for even `a` and the same type for odd `a`. The endpoints of `D_a`
have the same type for even `a` and different type for odd `a`. For a
same-type pair we chose corresponding multiplicity coordinates, so the
root commutes with all of `C`.

A different-type root centralizes `h` but does not normalize `C`.
Indeed conjugating a `C` matrix produces a nonzero cross-isotypic root
entry. Since the two order-nine groups have an order-three intersection
containing `<h>`, their intersection is exactly `<h>`. This proves the
support classification in `(QPF2)`.

For completeness, let `p_chi` be the Fourier projection of a character
`chi in dual(C)`. In the canonical group trace, the standard
double-coset calculation gives

```text
||p_psi v p_chi||_2^2
 = |C intersect v^(-1)Cv|/|C|^2                        (QPF8)
```

when the two characters agree on the intersection, and zero otherwise.
For a different-type root the intersection has order three. Agreement
on `<h>` leaves three target characters, each with squared norm

```text
3/9^2=1/27.
```

For a same-type root, `v` commutes with `C`. Only `psi=chi` survives,
and its squared norm is `9/9^2=1/9`. This gives every entry of the table.

Equivalently, normalize the mass matrix by

```text
M_v(psi,chi)=9||p_psi v p_chi||_2^2.
```

A complete row has entry `1/3` on each of the three equal-`h` targets,
and a diagonal row is the identity matrix. Both row and column sums are
one. Thus the vector `w_chi=1/9` is stationary for every displayed
root, and every uniform Hall inequality is satisfied.

## The first new kernel word

Let `Q` be the order-32 packet of the directed-cycle proof and put

```text
widehat Gamma=K *_(<h,D_0>) (<h> times Q).               (QPF9)
```

Here `K` is the finite scalar/qutrit head. This is the original
finite-vertex shadow. In the concrete Leavitt group,

```text
P Y_(0,r)P^(-1)=Y_(1,r)=x_(j,ell)(s_r)
```

acts between corresponding coordinates in two copies of the same
nontrivial `C`-module. Hence it commutes with `C`.

This commutation is not an amalgam normal-form consequence of `(QPF9)`.
After conjugating by `P^(-1)`, a candidate commutator has the form

```text
[Y_(0,r),P^(-1)cP].
```

The first letter is outside the edge because its coefficient is
nonconstant. Also `C'=P^(-1)CP` is not contained in the edge:
`C intersect C'=<h>`, while `C'` has order nine. Choose
`c in C` with `P^(-1)cP notin <h,D_0>`. The displayed commutator is
then a reduced alternating word of length four and is nontrivial in
`widehat Gamma`. One may take `c=J`: otherwise the conjugate central
line would be the leaf line, excluded by the fixed-space-rank theorem.
Thus `(QPF3)` is a genuine cross-translate kernel word.

## A finite-amalgam model of the flip

Let

```text
K_1=<C,P>,                    C'=P^(-1)CP.
```

Both are finite subgroups of `K`. The actor `P` fixes every
`h`-fixed coordinate setwise, so it centralizes `h` and
`<h> subset C intersect C'`. It does not normalize `C`: it sends the
trivial coordinate `i` to the nontrivial coordinate `j`, whereas any
normalizer of `C` preserves its trivial isotypic subspace. Therefore

```text
C intersect C'=<h>.                                      (QPF10)
```

The two roots `Y_(0,0),Y_(0,1)` commute and are independent involutions,
so

```text
A=<Y_(0,0),Y_(0,1)> isomorphic to C_2^2.
```

Moreover they commute with `C'`, because their `P`-conjugates act
between corresponding nontrivial `C` coordinates. Hence the concrete
relations define a surjection

```text
Gamma_Y=K_1 *_(C') (C' times A)
       -> <C,P,Y_(0,0),Y_(0,1)>.                         (QPF11)
```

Both vertices and the edge in `Gamma_Y` are finite. Therefore
`Gamma_Y` is virtually free and residually finite.

The phase table is already exact in its canonical trace. For
`1!=y in A`, amalgam normal form and `(QPF10)` give

```text
C intersect yCy^(-1)=C intersect C'=<h>.                 (QPF12)
```

Indeed, if `c in C-C'`, then `ycy^(-1)` is a reduced word and cannot
return to the `K_1` vertex. On the other hand `y` commutes with `C'`.
Thus `y` has the complete `1/27` table. Since

```text
P y P^(-1) commutes with C,
```

its translate has the diagonal `1/9` table.

Finally, residual finiteness gives literal finite-dimensional
countermodels, not only an abstract permanence statement. Separate in
one finite quotient the finitely many nonidentity elements of `C` and
the finitely many unwanted words used in `(QPF12)`. The left regular
representation of that quotient restricts to a multiple of the regular
representation of `C`, so all nine atom weights are `1/9` and both
support tables remain exact.

Therefore the complete-to-diagonal flip and its actor covariance carry
no normalized-Hilbert--Schmidt obstruction. The unresolved relations
must use the `X` family together with more than one actor translate;
those are precisely the relations omitted from `Gamma_Y`.
