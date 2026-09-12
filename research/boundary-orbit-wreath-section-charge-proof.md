---
rg: 2
id: boundary-orbit-wreath-section-charge-proof
kind: route
title: Summing lamp exponents over regular table sections defines an integer character
target: boundary-orbit-wreath-actor-has-infinite-abelianization
requires:
  - boundary-orbit-cyclic-wreath-has-fp-simple-envelope
artifacts:
  - research/artifacts/boone-higman-boundary-wreath-germ-construction-2026-09-08.md
---

Use the faithful wreath realization H from the required claim's proof.
There is a homomorphism epsilon:H->Z given by total lamp exponent;
epsilon(gamma)=1 and epsilon(hat(g))=0. Actor conjugation only
permutes lamp coordinates, so this is indeed a homomorphism.

For any character epsilon of a self-similar group, the map

    T_epsilon(h)=sum_(z in Z) epsilon(h|z)

is a homomorphism: the product section formula permutes the summands
from one factor, and epsilon adds the two sections in each product.
Here T_epsilon agrees with epsilon on hat(G) and gamma, since all
sections of hat(g) belong to hat(G) and

    gamma|0=gamma, gamma|#=hat(x), gamma|y=1 otherwise.

Thus epsilon(h)=sum_z epsilon(h|z) for every h in H.

If an element of E has a regular table with sections h_1,...,h_l,
define chi to be sum_i epsilon(h_i). Expanding a table leaf replaces
one coefficient h by its first-level sections, preserving this sum.
Two tables for the same homeomorphism admit common refinement: refine
their domain cones to be compatible, then restrict further as needed;
on an identical domain cone the image cone and the actual suffix
homeomorphism are identical. Faithfulness of H identifies the resulting
coefficients. Hence chi is well defined independently of the table.

To compose two tables, refine the first range and second domain to a
common cone partition. The composite coefficients are pairwise products
of the refined coefficients, in an order possibly permuted by the
tables. Applying epsilon and summing proves chi(ef)=chi(e)+chi(f).

Gamma's one-cone table gives chi(gamma)=1. All table coefficients for
V_m(hat(G)) have zero epsilon, so chi vanishes on that subgroup.
Surjectivity and infinite index of the commutator subgroup follow.

This also explains exactly why the argument does not apply after
replicating every state r>1 times: then the sum of section charges
for gamma is r, whereas its own charge remains 1. The table-refinement
invariance fails. This is a distinction between two tree actions of
the same abstract wreath product, not a contradiction between their
abelianizations.
