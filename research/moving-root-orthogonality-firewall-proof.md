---
rg: 2
id: moving-root-orthogonality-firewall-proof
kind: route
title: Hide a growing power relation beyond every fixed trace window
target: canonical-trace-does-not-control-moving-root-orthogonality
requires: []
---

Take, for example, primes `N` and `q_N=floor(sqrt(N))`, replacing `q_N` by
a neighboring nonzero residue if necessary.  For fixed `(a,b)` with
`b!=0`, the integer `a+q_N b` has absolute value strictly between zero and
`N` for all sufficiently large `N`; for `b=0,a!=0` the same is immediate.
This proves `(CMR1)` by the geometric-series trace of a clock matrix.

Since `N` is prime and `q_N` is nonzero modulo `N`, exponentiation by
`q_N` permutes the `N` spectral characters.  Hence `U_N` and `L_N` generate
the same diagonal algebra.  Their two `N`-dimensional `L^2` spaces have an
`N^2`-dimensional Hilbert tensor product, while multiplication lands in an
`N`-dimensional space, so it has a kernel and cannot be isometric.  The
relation `(CMR2)` is invisible to every fixed word because its exponent
depends on `N`.

