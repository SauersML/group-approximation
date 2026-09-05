---
rg: 2
id: exact-r-subalgebra-traces-via-x2
kind: route
title: A quasidiagonal trace on R restricts to a quasidiagonal trace on every subalgebra
target: separable-exact-subalgebras-of-r-have-quasidiagonal-trace
requires: [stw99-problem-x2-hyperfinite-factor-quasidiagonal]
---

By the remark of STW after Problem IX, quasidiagonality of `R` is the same
as quasidiagonality of its unique faithful trace `tau_R`: quasidiagonal
models of `R` have tracial weak-* limits, hence converge to `tau_R`, and
conversely models of the trace are asymptotically isometric because
`||a|| = lim_k tau_R((a^*a)^k)^(1/2k)` for the faithful trace.  If `tau_R` is
a quasidiagonal trace with models `phi_n : R -> M_(k_n)`, then the
restrictions `phi_n|_S` are u.c.p., asymptotically multiplicative in operator
norm on `S`, and their traces converge to `tau_R|_S`.  Exactness of `S` is
not used on this route.
