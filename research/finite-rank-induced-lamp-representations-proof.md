---
rg: 2
id: finite-rank-induced-lamp-representations-proof
kind: route
title: Separate lamp coefficients by induced finite-dimensional representations with finite-rank augmentation error
target: rf-lamps-with-finite-stabilizers-preserve-direct-finiteness
requires:
  - one-invertible-certificate-fiber-forces-global-invertibility
---

Write N=direct_sum_X A, let alpha be the permutation action of G on N,
and write elements of W as n u_g. Let pi:k[W]->k[G] be lamp augmentation.
Choose a finite set F subset X, a finite-dimensional representation of
k[A^F] on a nonzero vector space V, and extend it to

    rho:k[N]->End_k(V)

by augmenting every lamp outside F. Projection N->A^F is a group
homomorphism because distinct lamp factors commute, even when A is
nonabelian. Thus rho is a unital algebra representation.

## Induction retains a finite-rank error

On E=k^(G) tensor V, the space of finitely supported V-valued functions
on G, define

    (T_rho(n u_g)v)_h = rho(alpha_(h^(-1))(n)) v_(g^(-1)h).  (RIL1)

This is a representation. Composing n u_g and m u_t gives the product
coefficient

    rho(alpha_(h^(-1))(n)) rho(alpha_(h^(-1)g)(m))
      =rho(alpha_(h^(-1))(n alpha_g(m))),

and the input index becomes (gt)^(-1)h, as required by the semidirect
product law. All operators preserve finite support.

If n has finite lamp support S, its coefficient in (RIL1) is I_V
unless alpha_(h^(-1))(n) has support meeting F. The exceptional h lie in

    {h : hF intersects S}
      = union_(s in S,f in F) {h : hf=s}.                 (RIL2)

Each nonempty transporter in (RIL2) is a coset of the finite stabilizer
G_f, so this union is finite. Consequently T_rho(n u_g) differs by
finite rank from lambda(g) tensor I_V. By linearity, for every z in
k[W],

    T_rho(z) - (lambda(pi(z)) tensor I_V)

has finite rank. This remains true for fixed finite matrices of such
operators. Here lambda is the left regular action on k^(G).

## A one-sided inverse becomes two-sided in each representation

Suppose BA=I_n in M_n(k[W]), and assume M_n(k[G]) is directly finite.
Then pi(B)pi(A)=I_n implies pi(A)pi(B)=I_n. The reference operator

    A_0=lambda(pi(A)) tensor I_V

on E^n is therefore invertible, with inverse lambda(pi(B)) tensor I_V.
The represented operator T_rho(A) is injective because T_rho(B) is a
left inverse, and it differs from A_0 by finite rank. The elementary
finite-rank lemma in `finite-rank-certificate-perturbation-proof`
makes it bijective. Its given left inverse is therefore a right inverse:

    T_rho(AB-I_n)=0.                                     (RIL3)

The size n assumption on k[G] suffices. Tensoring its already exhibited
inverse with I_V requires no additional hypothesis at a larger matrix
size.

## These representations separate the full group algebra

Let z=sum_g a_g u_g be nonzero, with a_g in k[N], and choose a_(g_0)!=0.
Choose F containing all lamp sites appearing in its finite support.
Residual finiteness of A gives a finite quotient A->L injective on the
finite set of lamp values occurring there: separate every unequal pair
by a finite quotient and take the image in their finite product.
Distinct tuples in the support of a_(g_0) remain distinct in L^F.
Its image in k[L^F] is therefore nonzero, in any characteristic.

Use the left regular representation of k[L^F] to define rho. It is
finite-dimensional and rho(a_(g_0))!=0. At output h=1 in (RIL1), an input
supported only at g_0^(-1) isolates this coefficient from every other
G-coefficient. Choosing its value in V appropriately gives T_rho(z)!=0.
Thus the family of all these T_rho is jointly faithful. The same applies
entrywise to matrices.

Equation (RIL3) for every rho now forces AB=I_n in k[W]. Conversely,
k[G] embeds unitally in k[W], so direct finiteness at each size descends
to k[G]. This proves the equivalence. Empty X or a trivial lamp group
causes no exception: then W=G.
