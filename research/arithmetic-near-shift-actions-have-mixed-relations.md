---
rg: 2
id: arithmetic-near-shift-actions-have-mixed-relations
kind: claim
title: Residue-affine permutations force explicit mixed commutation relations with powers of the cofinite shift
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Let lambda be a permutation of N with eventual formulas

    lambda(m*k+r)=a_r*k+b_r,      a_r>0 integers,

and put A=lcm_r(a_r). For the cofinite shift s:n->n+1,

    [lambda*s^m*lambda^-1, s^A]=1

in NearSym(N). If lambda=lambda_g for a nonidentity element g
of an infinite regular input P, this is a nonidentity reduced word
of P*<s> killed in R_nu. Thus an arithmetic regular action with
a nontrivial such generator cannot have free-product near group.

For each nonidentity factor element a in the specified bijective-base
A_5*A_5 enumeration, one may take m=118 and A=6962. In particular

    [lambda_a*s^118*lambda_a^-1, s^6962]=1.

The arithmetic benchmark therefore avoids the free-near-shift
obstruction to finite presentation. Neither this relation nor that
avoidance proves its envelope finitely presented.
