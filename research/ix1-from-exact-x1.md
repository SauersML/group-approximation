---
rg: 2
id: ix1-from-exact-x1
kind: route
title: Nuclear traces are amenable, so the exact residual of X(1) makes a faithful trace quasidiagonal and the algebra with it
target: stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal
requires: [amenable-traces-on-exact-cstar-algebras-are-quasidiagonal]
---

Let `A` be separable nuclear with a faithful trace `tau`.  Every trace on a
nuclear C*-algebra is amenable (Brown, Proposition 3.5.1: the identity map
factors approximately through matrix algebras by u.c.p. maps, and the
composites are the required models).  `A` is exact, so the prerequisite
makes `tau` a quasidiagonal trace: u.c.p. maps `phi_n : A -> M_(k_n)`,
asymptotically multiplicative in operator norm, with `tr o phi_n -> tau`.

A faithful quasidiagonal trace makes the algebra quasidiagonal.  For
`a in A` and `k >= 1`, asymptotic multiplicativity gives
`tr(phi_n(a^*a)^k) - tr(phi_n((a^*a)^k)) -> 0`, hence
`liminf_n ||phi_n(a)||^(2k) >= tau((a^*a)^k)`.  Faithfulness of `tau` gives
`tau((a^*a)^k)^(1/k) -> ||a^*a||`, since for every `epsilon > 0` a bump
function `f` supported near `||a^*a||` has `tau(f(a^*a)) > 0` and
`(a^*a)^k >= (||a^*a|| - epsilon)^k f(a^*a)`.  So `||phi_n(a)|| -> ||a||`
for every `a`, and the maps `phi_n` are asymptotically multiplicative and
asymptotically isometric: `A` is quasidiagonal (Voiculescu's abstract
characterization).

Thus the exact residual of Problem X(1) implies Problem IX(1), exactly as
the universal X(1) did before its refutation; and through
`exact-r-subalgebra-traces-via-exact-x1` and
`exact-x1-from-r-exact-subalgebra-traces` so does the statement that the
trace of `R` is quasidiagonal on every separable exact subalgebra.
