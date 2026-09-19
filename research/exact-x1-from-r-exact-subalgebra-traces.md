---
rg: 2
id: exact-x1-from-r-exact-subalgebra-traces
kind: route
title: Reduce to a faithful trace with injective GNS closure, embed that closure in R, and restrict the trace of R
target: amenable-traces-on-exact-cstar-algebras-are-quasidiagonal
requires: [separable-exact-subalgebras-of-r-have-quasidiagonal-trace]
---

Let `A` be exact and `tau` amenable.  By
`directed-unions-preserve-trace-approximations` an amenable non-quasidiagonal
trace restricts to one on a separable unital subalgebra, which is again
exact, so assume `A` separable and unital.  Let `q : A -> B = pi_tau(A)` be
the GNS quotient with induced faithful trace `tau_B`.  Since `A` is exact,
`q` is locally liftable (Effros--Haagerup), so `tau_B` is amenable
(`amenable-trace-descends-through-locally-liftable-quotient`), and `B` is
exact.  For exact `B` amenability of `tau_B` is injectivity of
`N = pi_(tau_B)(B)''` (Brown, Corollary 4.3.4).  `N` is a finite injective
von Neumann algebra with separable predual and the faithful normal trace
`tau_B`, so it embeds trace-preservingly into the hyperfinite II1 factor:
its type II1 part is hyperfinite by Connes, its type I part is a direct sum
of matrix algebras and abelian algebras, and every faithful normal tracial
state on such an algebra is realized inside `R` by choosing projections of
the prescribed traces.  Thus `B subset N subset R` with `tau_R|_B = tau_B`.
The prerequisite makes `tau_B` quasidiagonal on `B`, and `tau = tau_B o q`
is then quasidiagonal on `A` by composing the models with `q`.

Together with `exact-r-subalgebra-traces-via-exact-x1` this makes the two
claims equivalent: the exact residual of Problem X(1) is exactly the
statement that the trace of `R` is quasidiagonal on every separable exact
subalgebra.
