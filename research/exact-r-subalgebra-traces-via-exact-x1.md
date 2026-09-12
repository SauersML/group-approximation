---
rg: 2
id: exact-r-subalgebra-traces-via-exact-x1
kind: route
title: Restrict the trace of R, note its GNS closure is injective, and apply the exact residual of X(1)
target: separable-exact-subalgebras-of-r-have-quasidiagonal-trace
requires: [amenable-traces-on-exact-cstar-algebras-are-quasidiagonal]
---

Let `S subset R` be separable and exact and `tau = tau_R|_S`.  The GNS
space `L^2(S,tau)` is the closure of `S` in `L^2(R,tau_R)`, and restriction
to it is a normal *-homomorphism from `W*(S) subset R` onto `pi_tau(S)''`,
injective because a von Neumann algebra element killing the cyclic vector has
zero trace-norm.  So `pi_tau(S)''` is isomorphic to `W*(S)`, which is
injective: `R` is injective and the trace-preserving conditional expectation
onto `W*(S)` passes injectivity to it.  For exact `S`, injectivity of the GNS
closure is amenability of the trace (Brown, Corollary 4.3.4).  The
prerequisite then makes `tau` quasidiagonal.
