---
rg: 2
id: zigzag-cyclic-shift-four-ray-proof
kind: route
title: Identify the cyclic generator on four rays and compute its full-rank translation lattice
target: zigzag-cyclic-shift-envelope-is-finitely-presented
requires: [mallery-zaremsky-shift-similar-envelope]
artifacts:
  - research/artifacts/boone-higman-zigzag-shift-compiler-2026-09-08.md
---

Write alpha for the slide (... 6 4 2 1 3 5 7 ...), lambda for the flip
(1 2)(3 4)..., and tau=(1 2). These generate E_2. The alpha-conjugates
of tau are adjacent transpositions along a single bi-infinite orbit,
so alpha and tau already generate all finitary permutations.

Let beta be the permutation induced by k->k+1 on the even copy of Z
through the stated nu, fixing every odd number. Direct substitution gives

    beta(4j+2)=4j+6     for j>=0,
    beta(4j)=4j-4       for j>=2,
    beta(4)=2.

Thus beta is eventually 4-periodic, as are alpha and lambda, and

    G=E_nu(Z)=<alpha,lambda,tau,beta> <= E_4.

Identify ray i with numbers 4k+i, i=1,2,3,4 and k>=0. The germ quotient
of E_4 by the finitary permutations is A_3 semidirect S_4, where

    A_3={t in Z^4 : sum_i t_i=0}.

Represent a germ by (sigma,t), meaning (i,k)->(sigma(i),k+t_i).
The generator germs are

    alpha:  sigma=(1 3)(2 4), t=(0,-1,1,0);
    lambda: sigma=(1 2)(3 4), t=(0,0,0,0);
    beta:   sigma=id,         t=(0,1,0,-1).

The germ image contains translations

    a=alpha^2:          (1,-1,1,-1),
    b=beta:             (0,1,0,-1),
    c=lambda beta lambda: (1,0,-1,0).

Let L=<a,b,c> in A_3. In the basis e1-e2,e2-e3,e3-e4 these vectors
have coordinates (1,0,1), (0,1,1), (1,1,0). Their determinant is -2,
so [A_3:L]=2.

L is normal in the generated germ group: conjugation by alpha fixes a
and negates b,c; conjugation by lambda negates a and interchanges b,c.
Modulo L, beta vanishes and alpha,lambda are commuting involutions,
since alpha^2=a, lambda^2=1 and (alpha lambda)^2=1. Their ray
permutations generate the Klein four group, so the germ group modulo L
is exactly that four group. Its translation kernel is therefore exactly L.

Consequently its index in A_3 semidirect S_4 is 2*(24/4)=12. G contains
the whole finitary kernel, so [E_4:G]=12 as well.

By Mallery-Zaremsky Lemma 3.9, E_4 is a finite extension of H_4.
Brown's finiteness theorem gives H_4 type F_3 and not FP_4. These
properties pass across finite-index subgroups and finite extensions;
hence they hold for G. In particular G is finitely presented. Strong
shift-similarity follows from the Mallery-Zaremsky construction.

Source details: Mallery-Zaremsky, arXiv:2202.00822v2, Lemma 3.9,
Observation 3.24, Proposition 3.27 and Example 3.31. Brown's result is
explicitly recalled in Cox-Kropholler-Martino, arXiv:2508.07816v1,
Introduction. This proof uses their stated finiteness theorem; it does
not claim a new proof of Brown's theorem.

The exact integer determinant and the image of order 16 in the finite
quotient of order 192 are independently checked by
experiments/bh_shift_cyclic_check.py. The permutation formulas and the
identification of the infinite group are proved above, not inferred
from testing finitely many points.

