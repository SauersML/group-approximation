---
rg: 2
id: agent-leavitt-not-local-context-pvms
kind: claim
title: Every local BCS context has explicit projections in the marked negative spin corner
distinct_from:
  agent-leavitt-local-spin-corner: that constructs and identifies the nested full matrix reservoir; this writes the actual joint spectral projections for every local BCS predicate and identifies the exact overlap obstruction.
  agent-leavitt-not-bcs-negative-root-corner: that asks for one globally overlap-consistent copy of the non-CE BCS algebra in the entire negative Hecke corner; this solves all context relations before overlap identification, but proves that the displayed common diagonal atlas cannot solve the overlap equations.
---

Let `B` be any finite binary constraint system with nonempty allowed-assignment
sets `R_c subset {+1,-1}^(U_c)`.  In the notation of
`agent-leavitt-local-spin-corner`, choose `d` with

```text
2^d >= max_c |R_c|.                                      (LCP1)
```

There are explicit finite group-ring projections

```text
p_(c,a) in P C[E_d]P subset P C[Delta]P,
             c a context,  a in R_c,                    (LCP2)
```

such that for every fixed `c` they are nonzero, mutually orthogonal, and sum
to `P`.  Consequently

```text
V_(c,x)=sum_(a in R_c) a(x)p_(c,a),       x in U_c,      (LCP3)
```

are commuting self-adjoint involutions in the unital corner `P C[Delta]P`
and satisfy the predicate of context `c` exactly.  Thus every local relation
of the fixed `B_loop` has a finite, literal projection realization inside one
common marked negative root corner.

The construction cannot by itself impose

```text
V_(c,x)=V_(c',x) whenever x belongs to U_c intersect U_(c'). (LCP4)
```

Indeed all displayed projections lie in one common diagonal algebra.  If
`(LCP4)` held, evaluation at any one of its minimal atoms would give a single
classical assignment satisfying every context.  In particular `(LCP4)` is
impossible for `B_loop`, since its strict finite-dimensional synchronous gap
rules out a perfect classical strategy.  The remaining negative-corner gate
is therefore exactly a noncommutative overlap-gluing problem, not a shortage
of finite projection capacity or a failure of any individual predicate.

