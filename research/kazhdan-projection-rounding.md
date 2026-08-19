---
rg: 2
id: kazhdan-projection-rounding
kind: claim
title: Almost-invariant projections round into the relative commutant
distinct_from:
  kazhdan-asymptotic-commutant-transport: That transports asymptotic commutants along a compressor in an operator-norm asymptotic representation; this is a single-step quantitative rounding inside one finite tracial algebra, with no compressor and no asymptotics.
  commutant-projection-extraction: That asks for projections inside the relative commutant of a central mark; this produces one from an almost-invariant projection anywhere in the algebra, with a constant depending only on the Kazhdan constant.
  invariant-size-collapse: That is the collapse principle for a conjugation-invariant monotone size; this is an analytic approximation statement and says nothing about compressions.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Let `Gamma` have property `(T)` with Kazhdan set `S` and constant `kappa`,
let `pi:G->U(M)` with `M` finite tracial, and `N=M cap pi(Gamma)'`.  For every
projection `p in M` there is a projection `q in N` with

```text
||p-q||_2 <= (1+sqrt2) kappa^(-1) max_(s in S) ||[pi(s),p]||_2.
```

The proof is three exact steps: property `(T)` applied to the trace-preserving
action on `L^2(M)`, whose fixed space is `L^2(N)` and whose orthogonal
projection is the conditional expectation `E_N`; the identity
`||p-E_N(p)||_2^2 = tau(a(1-a))` for `a=E_N(p)`, which uses only that `E_N` is
a trace-preserving `N`-bimodule map; and spectral rounding of `a` at `1/2`,
using `(t-chi_([1/2,1])(t))^2 <= 2t(1-t)` on `[0,1]`.

**Scope, which is the point.**  This is the conditional-expectation form of
the gap, and it does *not* give a trace dichotomy.  Concluding that `tau(p)`
is near `0` or `1` needs `N` to have no projection of intermediate trace, and
a diffuse `N` carries projections of every trace in `[0,1]`.  So the obstacle
in converting spectral gap into "small commutator energy implies small trace
on one side" is not the vector-state form of `(T)` -- that upgrades cleanly --
but the structure of the relative commutant, which is the same missing input
recorded by `invariant-size-collapse`.
