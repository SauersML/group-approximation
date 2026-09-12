---
rg: 2
id: diagonal-tensor-orbit-corner-induction-proof
kind: route
title: Keep the same group translation in every marked-site factor and induct through stabilizer corners
target: rf-lamps-preserve-stable-finiteness-for-arbitrary-actions
requires:
  - split-local-corner-extensions-preserve-stable-finiteness
---

Assume k[G] is stably finite. Every k[H], H<=G, is then stably finite
as a unital subalgebra. All tensor products below are over k.

## The base coefficients need no product closure of G

For any finite j, residual finiteness of A^j gives algebra maps

    k[A^j x H] -> k[L x H]

over its finite group quotients L, with jointly zero kernels. Indeed,
one quotient separates the finite A^j-support of a selected nonzero
H-coefficient. The finite-group left regular representation embeds
k[L] into M_(|L|)(k), hence embeds k[L x H] into M_(|L|)(k[H]).
This last ring is stably finite, in every characteristic. Joint
separation of the possible reverse inverse defect proves that

    k[A^j x H] is stably finite for all H<=G and j>=0.     (DWI2)

This is the only step that uses residual finiteness of A. It uses no
semisimplicity of finite group algebras. More generally (DWI2) itself
is a sufficient base hypothesis for the rest of the proof.

## The simultaneous induction

Let D=direct_sum_(x in X) k[A] with coordinatewise multiplication, and
C=k plus D its external unitization:

    (lambda,d)(mu,e)=(lambda mu,lambda e+mu d+de).

View C as k[A]-valued functions on X together with an extra point
infinity, equal to the scalar infinity value except at finitely many
sites. The extra point is present even if X is finite. Evaluation at
infinity is a split unital map C->k with kernel D. The G-action permutes
sites and fixes scalars.

For H<=G and j,r>=0 put

    R_r(H,j)=(k[A^j] tensor C^(tensor r)) semidirect H,

where H acts trivially on k[A^j] and diagonally on the C factors. We
prove these rings stably finite by induction on r simultaneously for
every H and j. For r=0 they are exactly the rings in (DWI2).

For r>=1 write K=k[A^j] tensor C^(tensor(r-1)), carrying its H-action.
After reordering tensor factors, R_r(H,j)=(C tensor K) semidirect H.
Applying C->k gives a split exact sequence of unital algebras

    0 -> J=(D tensor K) semidirect H
      -> R_r(H,j) -> R_(r-1)(H,j) -> 0.                 (DWI3)

The section inserts the identity of C, so it commutes with the H-action.
The quotient is stably finite by induction.

## The ideal formula includes the action on the other factors

For each H-orbit O in X choose o in O and t_x in H with t_x o=x.
Write H_o for its stabilizer. In the x-coordinate of D write e_x a
for a in k[A]. A term (e_x a tensor b)u_h in J maps to

    E_(x,y)((a tensor alpha_(t_x^(-1))(b))
                  u_(t_x^(-1) h t_y)),
                    y=h^(-1)x,                         (DWI4)

in Mat_fin(O,(k[A] tensor K) semidirect H_o). The last group element
fixes o. The internal k[A] factor has trivial H_o-action; all twisting
on K has been retained in (DWI4).

To verify multiplication, the product of an x,h term and a z,l term
vanishes unless z=h^(-1)x=y. When this condition holds, its K-coefficient
before transport is b alpha_h(b'). In the target, writing
q=t_x^(-1) h t_y, the coefficient is

    alpha_(t_x^(-1))(b) alpha_q(alpha_(t_y^(-1))(b'))
      =alpha_(t_x^(-1))(b alpha_h(b')).

The A-coefficients multiply in their original order and the stabilizer
tags multiply to t_x^(-1) h l t_w. This is exactly (DWI4) for the product.
Conversely every matrix term E_(x,y)((a tensor b)u_q) is obtained by
taking h=t_x q t_y^(-1) and undoing alpha_(t_x^(-1)) on b. Hence

    J ~= direct_sum_(O in H\X)
             Mat_fin(O,R_(r-1)(H_o,j+1)).               (DWI5)

All matrices have finite total support. A finite sum of diagonal units
covers every finite set of elements of J; its corner is a finite product
of finite matrix rings over the coefficients in (DWI5). Those coefficients
are stably finite by induction, since H_o<=G. The split local-corner
extension lemma applies to (DWI3), proving the induction step.

In particular T_r=(C^(tensor r)) semidirect G=R_r(G,0) is stably finite
for every r. This proof concerns these specific diagonal crossed
products, not arbitrary tensor products of stably finite algebras.

## Marked tuples separate the wreath algebra

Let N=direct_sum_X A. For n in N, define the unit v_n of C by
v_n(x)=[n(x)] and v_n(infinity)=1. The map n->v_n is a group homomorphism,
including when A is nonabelian, and is equivariant for the site action.
Consequently

    n g -> v_n^(tensor r) u_g

is a group homomorphism W->T_r^x and extends linearly to
Phi_r:k[W]->T_r. Use Phi_0=pi:k[W]->k[G], the lamp augmentation.
There is only one formal base tag g in these targets; the same g acts
on all tensor factors.

For a nonzero z=sum_g b_g[g], choose a finite set F containing every
lamp site in all of its coefficient supports. If F is nonempty,
enumerate its distinct sites as x_1,...,x_r and evaluate the r factors
of C at those sites. On the image of k[A^F], this coefficient evaluation
is exactly

    k[A^F] -> k[A^r],
    [n] -> [n(x_1)] tensor ... tensor [n(x_r)],

an isomorphism. Some nonzero b_g therefore has a nonzero image in its
coefficient of u_g, and Phi_r(z)!=0. Different g remain independent
formal group tags, irrespective of tuple stabilizers. Evaluation is
only used on coefficients and need not extend to the crossed product.
If F is empty, Phi_0 already detects z.

Thus intersection_(r>=0) ker Phi_r=0. Given BA=I over a finite matrix
ring of k[W], each stably finite T_r makes Phi_r(AB-I)=0. Entrywise
separation gives AB=I. Conversely, k[G] embeds unitally into k[W], so
stable finiteness of k[W] implies stable finiteness of k[G].

## Arbitrarily indexed permutation certificates

To prove (DWI1), choose a finite elementary abelian group L with enough
characters to map onto B. In characteristic different from two, use
L=(C_2)^a with |L|>=|B|; all its characters lie in k. In characteristic
two, use L=(C_3)^a and a finite extension K/k containing a primitive cube
root of unity. In the first case put K=k. Always char(k) does not divide
|L|. If d=[K:k], restriction of scalars embeds K[G] into M_d(k[G]), so
K[G] is stably finite under the standing hypothesis.

The proved wreath theorem makes K[L wr_X G] stably finite. Finite Fourier
transform at each lamp site gives the equivariant algebra isomorphism

    K[direct_sum_X L] ~= C_lc(Lhat^X,K).

For example, the indicator of character chi at site x corresponds to
|L|^(-1) sum_(l in L) chi(l)^(-1)[l at x]. Products of these indicators
give every finite-pattern function; compactness makes every locally
constant function depend on a finite pattern. Thus Fourier extends to
the crossed products by G for this arbitrary permutation action.

Choose a surjection Lhat->B. Its coordinatewise extension Lhat^X->B^X
is equivariant and onto. Pullback of coefficients, followed by k->K,
therefore embeds C_lc(B^X,k) semidirect G into K[L wr_X G]. Stable
finiteness descends to this subalgebra. Conversely k[G] embeds as the
constant coefficients, proving (DWI1). No extra assertion about an
individual constant-evaluation map follows from this global equivalence.
