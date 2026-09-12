---
rg: 2
id: finite-particle-wreath-separation-proof
kind: route
title: Separate lamp coefficients by finite marked-site tensors of split local-corner algebras
target: rf-lamp-permutational-wreaths-satisfy-stable-finiteness
requires:
  - split-local-corner-extensions-preserve-stable-finiteness
---

## The auxiliary algebra for one marked site

Write D=direct_sum_(x in X) k[A], with coordinatewise multiplication, and
let C=k plus D be its external unitization. Explicitly,

    (lambda,d)(mu,e)=(lambda mu,lambda e+mu d+de).

It is useful to view C as functions on X union {infinity} taking values
in k[A], equal to the scalar value at infinity outside a finite set.
This uses an extra infinity coordinate even when X is finite. Evaluation
at infinity is a split unital map C->k with kernel D.

The G-action on X permutes the coordinates of D and fixes scalars. Form
the algebraic crossed product R=C semidirect G, with formal units u_g.
The induced sequence

    0 -> J=D semidirect G -> R -> k[G] -> 0             (FPW1)

has a unital section sending [g] to u_g. For x in X write e_x for the
identity of its coordinate copy of k[A]. These are orthogonal idempotents.

## The ideal consists of matrix algebras over stabilizers

For each G-orbit O choose o in O and t_x in G with t_x o=x.
Let H=G_o. An element e_x a u_g of J, with a in the x-coordinate copy
of k[A], maps to

    E_(x,y) (a [t_x^(-1) g t_y]),    y=g^(-1)x,

in the algebra Mat_fin(O,k[A x H]). The bracketed group element belongs
to H. The action on the internal copy of A is trivial, so its group
algebra commutes with k[H] in the coefficient algebra.

Multiplication in the crossed product is zero between two such terms
unless the source of the first arrow is the target of the second.
When those match, the displayed H-elements multiply exactly as matrix
coefficients. Conversely every matrix coefficient E_(x,y)(a[h]) comes
from g=t_x h t_y^(-1). Thus this is an algebra isomorphism, giving

    J ~= direct_sum_(O in G\X) Mat_fin(O,k[A x G_o]).   (FPW2)

All matrices here have finite total support, not merely finite support
in each row. This is why diagonal matrix units give local units for J.

## All finite tensor powers retain stable finiteness

We prove by induction on r that, for every residually finite group H,

    S(H,r)=k[H] tensor_k R^(tensor r)

is stably finite. Tensor power zero means k, so S(H,0)=k[H].
This base case follows directly from residual finiteness: a finite quotient
can separate the finite support of any proposed nonzero inverse defect,
while its group algebra is finite-dimensional and stably finite.

For the induction step, tensor (FPW1) with S(H,r-1). Tensoring over a
field is exact and preserves the unital section. The quotient is

    S(H,r-1) tensor k[G] ~= S(H x G,r-1),

which is stably finite by induction. By (FPW2) the ideal is

    direct_sum_O Mat_fin(O,S(H x A x G_o,r-1)).

Every group H x A x G_o is residually finite: subgroups and finite direct
products of residually finite groups are residually finite. Consequently
each coefficient ring in this ideal is stably finite by induction. Its
finite diagonal corners are therefore stably finite. Apply
split-local-corner-extensions-preserve-stable-finiteness to obtain the
induction step. Taking H trivial proves that every R^(tensor r) is stably
finite. This argument does not assume that a tensor product of two
arbitrary stably finite algebras is stably finite; it proves the specific
tensor statement using the split sequences and the strengthened induction.

## Map the wreath product into each tensor algebra

Put N=direct_sum_X A and W=N semidirect G. A lamp configuration n in N
gives a unit v_n of C whose value at x is the basis unit [n(x)] of k[A]
and whose value at infinity is 1. This belongs to C because n has finite
site support. The map n->v_n is a group homomorphism even if A is nonabelian.
Covariance u_g v_n u_g^(-1)=v_(g.n) gives a homomorphism

    phi:W->R^x,       phi(n g)=v_n u_g.

For each r>=1 the group homomorphism w->phi(w)^(tensor r) extends linearly
to a unital algebra homomorphism Phi_r:k[W]->R^(tensor r). Under

    R^(tensor r) ~= (C^(tensor r)) semidirect G^r,

the base group element g is tagged by the formal group element
(g,...,g) of G^r. Distinct g therefore remain linearly independent over
the coefficient algebra, regardless of stabilizers of tuples of sites.

## A finite tuple detects any nonzero element

Write a nonzero z in k[W] uniquely as sum_g b_g[g], with b_g in k[N]
and only finitely many nonzero b_g. There is a finite set F subset X
containing every lamp site in the support of every b_g.

If F={x_1,...,x_r} is nonempty, evaluate the r coefficient factors C at
these distinct sites, obtaining an algebra map C^(tensor r)->k[A^r].
For every n supported on F, it sends v_n^(tensor r) to

    [n(x_1)] tensor ... tensor [n(x_r)].

Thus on k[A^F] it is exactly the canonical isomorphism k[A^F]->k[A^r].
Choose g with b_g!=0. Evaluation of the coefficient of the formal tag
(g,...,g) in Phi_r(z) is nonzero, so Phi_r(z)!=0. Evaluation is used only
on coefficients; it need not extend equivariantly to the crossed product.
If F is empty, use r=1 and evaluation at infinity to detect the nonzero
scalar coefficient instead.

One marked site alone is not asserted to be faithful. For example, with
two binary lamps at x!=y the element (a_x-1)(a_y-1) maps to zero under
Phi_1 because e_x e_y=0. Under Phi_2, coefficient evaluation at (x,y)
gives (a-1) tensor (a-1), which is nonzero over every field, including
characteristic two. The tensor family is the essential separation step.

We have proved intersection_(r>=1) ker Phi_r=0. If B A=I in a matrix ring
over k[W], stable finiteness of every target gives Phi_r(A B-I)=0 for all
r. Entrywise separation forces A B=I. This proves the claimed stable
finiteness over every field.
