---
rg: 2
id: stw59-independent-component-and-degree-one-obstructions
kind: claim
title: Simple monotracial AH algebras have prescribed finite component groups and independently enlargeable free degree-one stabilization cokernels
distinct_from:
  stw59-exact-finite-abelian-unitary-component-groups: This computes the cokernel in degree one and allows order-one arms that preserve the finite component group while increasing the free higher obstruction.
  stw59-monotracial-matrix-stable-counterexamples: This detects failure of rational K-stability at matrix size one even when the scalar-unitary K1 map is bijective.
artifacts:
  - research/artifacts/stw59-persistent-euler-degree-one-cokernel-2026-09-05.md
---

For any finite list d_1,...,d_s>=1 with s>=1, there is a simple
unital separable nuclear stably finite monotracial AH algebra A with

    K1(A)=0,
    U(A)/U0(A)=direct sum_alpha Z/d_alpha,
    coker(pi_1 U(A)->K0(A))=Z^s.

The degree-one map is canonical stabilization followed by Bott
periodicity. Its image is exactly the kernel of an explicit Euler
surjection K0(A)->direct sum_alpha d_alpha Z. No calculation of
the degree-one kernel is asserted.

Every M_m(A), m>=2, is K-stable, whereas A is not rationally
K-stable. Its stable rank is exactly two, including when the finite
component group is zero. Setting all d_alpha=1
gives K1-bijective examples with degree-one cokernel Z^s.
Appending order-one factors increases s while preserving any
previously specified finite component group.

No pureness is asserted. This refines the LIX examples and does
not solve another named problem.

ROUTES

stw59-euler-kernel-persistence-degree-one-proof
