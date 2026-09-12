---
rg: 2
id: kazhdan-generator-containment-is-uniform-on-the-group
kind: claim
title: Exact Kazhdan representations turn generator near-containment in a subalgebra into uniform group near-containment
distinct_from:
  sl3-re-coprime-face-closes-under-log-rate: That telescopes a congruence representative and loses its logarithmic word length; this applies the Kazhdan estimate to the Jones projection and has no word-length or dimension loss.
  relative-fixed-algebra-payment-lemma: That estimates the distance of an operator to an adjoint fixed algebra; this changes the Hilbert space to the basic construction and estimates the distance of every group unitary to an arbitrary target subalgebra.
  congruence-slot-escapes-ultraproduct-lambda-algebra: That correctly separates the constant-sequence subgroup algebra from its coordinate algebra; this leaves that distinction intact and proves uniform containment in a separate coordinate carrier.
artifacts:
  - research/artifacts/kazhdan-jones-uniform-carrier-containment-2026-09-08.md
---

Let C have a finite Kazhdan pair (S,kappa), with the convention that
every unitary representation alpha obeys

    dist(xi,Fix(alpha)) <= kappa^(-1) max_(s in S)||alpha(s)xi-xi||.

Let (M,tau) be any finite tracial von Neumann algebra, let B be a
unital von Neumann subalgebra, and let rho:C->U(M) be a genuine
representation. Then

    sup_(c in C) dist_2(rho(c),B)
      <= (2/kappa) max_(s in S) dist_2(rho(s),B).          (KJC1)

The constant is independent of M, B, finite quotient size, and word
length. In particular the estimate applies to elements c_n varying
with the coordinate: if exact rho_n:C->U(M_n) have generators
asymptotically contained in B_n, then rho_n(c_n) is asymptotically
contained in B_n for every choice c_n in C.

More generally, for unitaries V_n and eta_n defined by

    eta_n=||V_n-rho_n(c_n)||_2,
    epsilon_n=max_(s in S)dist_2(rho_n(s),B_n),

one has

    dist_2(V_n,B_n) <= eta_n+2 epsilon_n/kappa.           (KJC2)

If the right hand side tends to zero, then
||E_(B_n)(V_n)||_2 tends to one. This rules out an expectation-zero
relative-embedding witness at any outside word that is approximated
by such coordinate group elements.

Exactness of rho is essential to this proof: conjugation by an
approximate representation does not define the unitary representation
on the Jones basic construction to which the Kazhdan estimate applies.
No assertion about arbitrary approximate representations or the full
unit ball of rho(C)'' is made.
