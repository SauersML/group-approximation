---
rg: 2
id: contracting-srn-stabilizer-ascending-hnn-proof
kind: route
title: A cofinal contraction makes the neighborhood kernel an ascending HNN extension up to cyclic germs
target: contracting-srn-rational-stabilizers-are-fp
requires: []
artifacts:
  - research/artifacts/boone-higman-boundary-wreath-germ-construction-2026-09-08.md
---

Write C={1,...,d}^N and B=V_d(G). A regular map on a cone has the form
alpha*z -> beta*g(z), g in G. Composition is from right to left.

## Imported facts and the additional step

[Belk--Matucci, Boone--Higman Embeddings for Contracting Self-Similar Groups](https://eprints.gla.ac.uk/349706/2/349706.pdf)
records Nekrashevych's finite-presentation theorem for B. Its Lemma 2
extends any finite family of prescribed regular maps between disjoint
cones when both unions are proper. Its Lemma 4 shows that, at a rational
point alpha*beta^infinity, the germ of the pure prefix map
alpha*z -> alpha*beta*z generates a finite-index cyclic subgroup of the
germ group. Proposition 6 concludes finite generation of rational-set
stabilizers. The HNN argument below is an additional step, not a quotation
of that proposition.

## The germ lattice

The empty-set case is B itself. Otherwise let F={p_1,...,p_k}, let
P=Fix_B(F), and let K be its subgroup consisting of elements equal to the
identity on some neighborhood of F. The joint germ map is

    pi: P -> product_i (B)_(p_i),       ker(pi)=K.

Choose a period-contraction germ t_i at each p_i as in Lemma 4. Each t_i
has infinite order. These germs are independently realizable in P: take
small disjoint cones around F, prescribe the contraction at one point and
the identity near all the others, and apply the cone extension lemma.
Consequently the image of pi contains

    D=product_i <t_i> = Z^k.

D has finite index in the product of germ groups. Its preimage P_0 has
finite index in P and P_0/K=D. Normality of D in the larger germ product
is not required.

## A finitely presented neighborhood subgroup with a cofinal contraction

Choose a proper clopen neighborhood U of F. If C minus U consists of r
cones, remove t further disjoint cones from U away from F, choosing
t >= 0 so r+t=1 modulo d-1. Such cones exist in arbitrary finite number.
Continue to denote the resulting neighborhood by U. Its complement has
a partition into r+t cones. A partition of C into exactly r+t cones
exists, so a finite prefix homeomorphism C minus U -> C identifies

    R=Fix_B(U) with B.

Indeed conjugating regular tables by that prefix homeomorphism preserves
their G sections, and extending by the identity on U gives the inverse
identification. Thus R is finitely presented.

Choose disjoint cones U_i=alpha_i*C inside U, with
p_i=alpha_i*beta_i^infinity, and put U_0=union_i U_i. They may be chosen
small enough that U_0 is proper. Prescribe s on U_i by

    s(alpha_i*z)=alpha_i*beta_i*z.

Partition U minus U_0 into finitely many cones and map each of these by
a pure prefix map into a different small cone in the nonempty annulus
U_0 minus union_i alpha_i*beta_i*C. There is room for any finite number
of such target cones. The entire prescribed domain is U, and its range
is a proper subset of U_0. The cone extension lemma, with identity
sections, completes these prescriptions to s in V_d <= B.

We have s(U) subset U_0 subset U. Subsequent iterates contract the period
at every p_i. Hence s^n(U) is eventually inside every neighborhood of F.
The joint germ of s is delta=(1,...,1) in D. Moreover

    R <= s*R*s^-1,        K = union_(n>=0) s^n*R*s^-n.

The second equality follows because membership in the right-hand
subgroup means being the identity on s^n(U), and these sets are cofinal
among neighborhoods of F.

## Finite presentation

Put L=<R,s>. The map phi:R->R, r |-> s^-1*r*s, is injective. The
ascending HNN presentation

    < R, u | u^-1*a*u=phi(a), a in a finite generating set of R >

is finite and maps onto L by u |-> s. It is injective: the ascending
normal form is u^i*r*u^-j, i,j>=0. If its image is the identity, its
joint germ is (i-j)*delta, so i=j; then r=1 in R. The same word is
therefore the identity in the HNN extension.

Thus L is finitely presented. The displayed union gives
L=pi^-1(<delta>) inside P_0. In particular L is normal in P_0, with

    P_0/L = D/<delta> = Z^(k-1).

An extension of a finitely presented kernel by a finitely presented
quotient is finitely presented: take presentations for both, lifts of
quotient generators, conjugation relations on the finite kernel
generating set, and one lifted relation for each quotient relator.
It follows that P_0 is finitely presented. Finite-index overgroups of
finitely presented groups are finitely presented, so P is as well.
The setwise stabilizer is a finite extension of P, completing the proof.
