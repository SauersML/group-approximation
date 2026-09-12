---
rg: 2
id: twisted-lamp-diagonal-corner-induction-proof
kind: route
title: Carry finite internal automorphism actions through every stabilizer corner
target: residual-lamp-quotients-handle-monomial-actions
requires:
  - split-local-corner-extensions-preserve-stable-finiteness
---

Assume k[G] is stably finite. First suppose A is finite. All tensor
products are over k. Let D=direct_sum_X k[A] with coordinatewise
multiplication and let C=k plus D be its external unitization. The
G-action on C is

    alpha_g(e_x a)=e_(gx) theta_(g,x)(a),

where theta also denotes the induced group algebra automorphism.
It fixes scalar multiples of the external identity. Evaluation at
infinity C->k is a split equivariant unital map with kernel D.

## Strengthen the induction to all finite auxiliary groups

For every H<=G, finite group F, homomorphism beta:H->Aut(F), and r>=0,
consider

    R_r(H,F,beta)=(k[F] tensor C^(tensor r)) semidirect H.

Here H acts by beta on k[F] and diagonally on the C factors. We prove
stable finiteness simultaneously for every H,F,beta by induction on r.
At r=0 the ring is k[F semidirect_beta H]. The subgroup H has finite
index |F|, so left multiplication on the free right k[H]-module with
basis F gives a faithful unital embedding

    k[F semidirect_beta H] -> M_(|F|)(k[H]).

Since k[H] is a unital subalgebra of k[G], the target is stably finite.
There is no semisimplicity or restriction on characteristic here.

For r>=1 set K=k[F] tensor C^(tensor(r-1)), with its H-action alpha.
The map C->k gives the split sequence

    0 -> J=(D tensor K) semidirect H
      -> (C tensor K) semidirect H -> K semidirect H -> 0.

The quotient is R_(r-1)(H,F,beta), stably finite by induction.

## Twisted orbit transport

For each H-orbit O in X choose o in O and t_x in H with t_x o=x.
The stabilizer H_o acts on A by h->theta_(h,o); the cocycle identity
makes this a homomorphism. It acts on A x F by theta_(h,o) x beta_h.
The O-summand of J is isomorphic to

    Mat_fin(O,(k[A] tensor K) semidirect H_o).

Explicitly, putting y=h^(-1)x, send (e_x a tensor b)u_h to

    E_(x,y)((theta_(t_x^(-1),x)(a)
                 tensor alpha_(t_x^(-1))(b))
                 u_(t_x^(-1) h t_y)).                   (TWI1)

The matrix product vanishes unless the column of the first term equals
the row of the second, exactly the condition that the original site
supports meet. In the nonzero case set q=t_x^(-1) h t_y. The identity

    theta_(t_x^(-1),x) theta_(h,y)
      =theta_(q,o) theta_(t_y^(-1),y)

follows from the action cocycle and verifies the A-coefficient product.
For K the corresponding identity is

    alpha_(t_x^(-1))(b) alpha_q(alpha_(t_y^(-1))(b'))
      =alpha_(t_x^(-1))(b alpha_h(b')).

The stabilizer tags multiply as required. Conversely any matrix term
is reached by taking h=t_x q t_y^(-1) and undoing the two automorphisms
on its coefficient, so (TWI1) is an isomorphism.

Its coefficient ring is R_(r-1)(H_o,A x F,beta'), with
beta'_h=theta_(h,o) x beta_h. The group A x F remains finite, so the
strengthened induction applies. Thus J is a direct sum of finite-support
matrix rings over stably finite rings. Finite sums of diagonal units
are cofinal idempotent local units with stably finite corners. The
split local-corner extension theorem proves the induction step.

## Marked-site separation still retains one G-tag

Taking F trivial and H=G proves that T_r=(C^(tensor r)) semidirect G
is stably finite. For n in N define v_n(infinity)=1 and v_n(x)=[n(x)].
Then v_n is a unit of C, the map n->v_n is a group homomorphism, and
alpha_g(v_n)=v_(g.n). Therefore

    Phi_r:k[W]->T_r,       Phi_r([ng])=v_n^(tensor r) u_g

is an algebra homomorphism. Set Phi_0 equal to lamp augmentation.

These maps jointly separate k[W]. For a nonzero sum z=sum_g b_g[g],
take the finite union S of the lamp sites occurring in its support.
If S is nonempty, enumerate its distinct sites x_1,...,x_r. Evaluating
the corresponding r coefficient factors at these sites is an
isomorphism on the embedded k[A^S], and detects a nonzero b_g. The
different formal u_g remain linearly independent. This coefficient
evaluation need not be a crossed-product map. If S is empty, Phi_0
detects z. Separation applied entrywise to AB-I whenever BA=I proves
stable finiteness of k[W] for finite A.

## Invariant finite quotients

Now allow arbitrary A with the stated invariant separating family M.
Close that family under finite intersections; its members remain
invariant finite-index normal subgroups and still separate A. Every
theta descends to A/M, yielding an exact quotient homomorphism from W
to the corresponding finite-lamp twisted wreath group W_M. Its group
algebra is stably finite by the finite case.

For a nonzero finite group algebra sum, choose M separating all
distinct values among the finitely many lamp values in its support,
including the identity. Such an M exists by separating their finitely
many nonidentity differences. Distinct lamp configurations remain
distinct, and all G-tags are unchanged. Hence k[W]->k[W_M] jointly
separate k[W]. They annihilate every possible reverse inverse defect,
which therefore vanishes in k[W] itself.

If A is finitely generated and residually finite, given a!=1 choose a
finite-index normal subgroup N not containing a. A finitely generated
group has only finitely many subgroups of each bounded finite index:
their coset actions are homomorphisms to a bounded finite collection
of symmetric groups and are specified by finitely many generator
images. Intersect all subgroups of index at most [A:N]. The result
is a characteristic finite-index subgroup contained in N. These
characteristic subgroups separate A and are invariant under all theta.

Finally k[G] embeds unitally into k[W], proving the converse in every
case. The proof gives stable finiteness and does not assert preservation
at the original fixed matrix size.
