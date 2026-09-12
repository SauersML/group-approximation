---
rg: 2
id: relative-automorphism-finite-relator-lifting-proof
kind: route
title: Lift finitely many automorphisms, inverses, and presentation relators to a finite base presentation
target: relative-automorphism-fp-host-reflects-base-presentation
requires: []
artifacts:
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

Write G=<a_1,...,a_d | R>, where R may be infinite, and let F(a) be the
free group on these symbols. Composition of automorphisms is alpha beta
=alpha after beta. Then tau_g tau_h=tau_(gh), and tau_g=1 implies g=1
by evaluating at x_1. Thus tau is an embedding.

Suppose tau(G)<=B<=Aut_G(G*F_n) and B is finitely presented. Choose a
finite presentation <Y | Q> for B whose generators include distinguished
symbols t_i representing tau_(a_i). Such a presentation exists by adding
finitely many generators with defining relations to any finite
presentation of B. The other generators are actual relative
automorphisms; no generation theorem for the full relative automorphism
group is required.

For each y in Y, choose words u_(y,j), v_(y,j) in F(a)*F(x_1,...,x_n)
representing y(x_j), y^-1(x_j). For t_i choose these words to be exactly
x_1*a_i and x_1*a_i^-1 at j=1, and x_j at the other indices.

The substitutions U_y, V_y sending x_j to these words and fixing all
a_i define endomorphisms of the free product F(a)*F(x). They need not
yet be automorphisms. Their induced endomorphisms on G*F_n are mutually
inverse. Consequently the following finite collection of words is trivial
in G*F_n:

1. U_y(V_y(x_j))*x_j^-1 and V_y(U_y(x_j))*x_j^-1 for all y,j;
2. Q_q(x_j)*x_j^-1 for all q in Q and all j, where Q_q substitutes U_y
   for y and V_y for y^-1 in the word q.

The kernel of F(a)*F(x)->G*F_n is the normal closure of R. Every word in
that normal closure is a finite product of conjugates of elements of R
and their inverses. Choose the finitely many such expressions needed for
the displayed collection, and let R_0 be the union of the relators of R
occurring in those expressions. This is a finite subset of R.

Put G_0=<a_1,...,a_d | R_0>. Every U_y and V_y descends to G_0*F_n:
the substitutions fix F(a) pointwise and therefore preserve the normal
closure of R_0. The identities in (1) hold in G_0*F_n. Since all base
generators are fixed, these identities on the x_j prove that the induced
maps are mutually inverse automorphisms of G_0*F_n fixing G_0.
The identities in (2) similarly prove all relators Q. We have obtained a
homomorphism

    L:B -> Aut_(G_0)(G_0*F_n)

which sends every distinguished t_i to the canonical translation by the
corresponding generator of G_0. No surjectivity of L is needed.

Now take any r in R, viewed as a word in the a_i. Since r=1 in G,
r(t_1,...,t_d)=tau_(r(a))=1 in the subgroup B. Apply L. Its image is
the canonical translation by r(a) in G_0, which must therefore be the
identity. Evaluating that translation at x_1 gives r(a)=1 in G_0.
Thus every relator of R is a consequence of R_0. Since R_0 is contained
in R, the natural quotient G_0->G is an isomorphism. This supplies a
finite presentation of G.

Taking B=A proves the necessary condition for the whole automorphism
group. For the converse when G is centerless, import Proposition 1.1 of
[Belk--Fournier-Facio--Hyde--Zaremsky](https://arxiv.org/html/2503.21882v2):
finite presentation of a centerless G implies finite presentation of
Aut_G(G*F_n).

The necessity proof is a finite-relator argument written here, not an
attribution to that proposition and not a claim of novelty. It is not
Lean-formalized. It does not assume that an arbitrary automorphism lifts
to an arbitrary finite approximation: the inverse identities are exactly
what selects an approximation where the chosen lifts are automorphisms.
