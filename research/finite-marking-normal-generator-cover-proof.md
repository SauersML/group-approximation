---
rg: 2
id: finite-marking-normal-generator-cover-proof
kind: route
title: Lift subgroup generators, impose their relators, and impose one normal-generation identity per cover generator
target: finite-marking-normal-generator-cover
requires: []
artifacts:
  - research/artifacts/boone-higman-steinberg-cover-correction-2026-09-08.md
---

Write P=<X|R> and H=<Y|T> with all four sets finite. For each y in Y
choose a word v_y in X whose image under pi is j(y). Let P_1 be the
quotient of P by the |T| relators t(v_y)=1.

Each added relator is killed by pi, so pi factors as P_1->Q. The
v_y define a homomorphism i_1:H->P_1 whose composite with P_1->Q is j.
Since j is injective, i_1 is injective. In particular h has a lift
h_1=i_1(h) belonging to the embedded H.

For each x in X, normal generation of Q supplies a finite identity
pi(x)=product(q_k j(h)^(epsilon_k) q_k^-1), epsilon_k in {1,-1}.
Lift each q_k to P_1 and call the resulting product of conjugates of
h_1 the word w_x. Form Gamma by adjoining the |X| relators x=w_x.

Again every new relator holds in Q, so the map to Q survives. The
composite H->Gamma->Q is j, which proves that H still embeds in Gamma.
Every generator of Gamma lies in the normal closure of the image of h,
so that image normally generates Gamma. The finite presentation and
the bound on added relators are immediate. Property (T) passes from P
to its quotient Gamma.
