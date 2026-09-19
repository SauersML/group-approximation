---
rg: 2
id: stw59-twisted-torsion-finite-test
kind: claim
title: The first projective twisted S4 unitary test reduces to a quotient of Z/24
artifacts:
  - research/artifacts/stw59-twisted-torsion-test-2026-09-05.md
---

Let u:S^4 -> U(2) generate pi_4(U(2)), based at 1. On
S^4 x CP^k put F_k=C^2 direct-sum L^{direct-sum 2} and
v_k=u direct-sum 1. These are images of u under the unital injective
twisted coordinate/point-evaluation map described in the artifact.
All v_k have zero K1 class; v_0 and v_1 are null-homotopic.

For k=2, set Z=(S^4 x CP^1) union ({x_0} x CP^2), and let D be
the image of the section-restriction boundary map
pi_1(U(Gamma(End(F_2|Z)))) -> pi_8(U(4))=Z/24.
Lifting the explicit contraction of v_2|Z gives q in Z/24 with

    v_2 is null-homotopic if and only if q is in D.

The coset q+D has order at most two. This reduction alone did not
compute q or D. The subsequent stw59-simple-ah-non-k1-injective
proof decides that q+D is nonzero of order two using mapping-torus
parity; it does not identify D as a particular subgroup of Z/24.
Nonzero c_2(L direct-sum L) alone obstructs only the particular
spare-line contraction and was not sufficient for the new conclusion.
