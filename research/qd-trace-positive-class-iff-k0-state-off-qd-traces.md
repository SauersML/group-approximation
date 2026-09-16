---
rg: 2
id: qd-trace-positive-class-iff-k0-state-off-qd-traces
kind: claim
title: An exact quasidiagonal algebra has a singular K_0-class positive on quasidiagonal traces iff some trace induces a K_0-state that no quasidiagonal trace induces
distinct_from:
  qd-nuclear-algebra-with-qd-trace-positive-singular-class: that is the open existence question; this is an algebra-by-algebra equivalence that restates it as a gap between two sets of K_0-states and constructs no algebra.
  blackadar-rordam-haagerup-k0-states-are-traces: that says every K_0-state of an exact stably finite algebra comes from some trace; this compares the K_0-states of all traces with those of the quasidiagonal traces.
  stw07-singular-classes-change-sign-or-sit-on-boundary: that bounds the sign pattern of one singular class over all traces; this uses it to show that a singular class positive on quasidiagonal traces exists exactly when the two K_0-state sets differ.
  stw07-trace-obstruction-forces-nonqd-trace-and-non-uct: that lists necessary consequences of a witness; this is a necessary and sufficient condition for a given algebra.
artifacts:
  - research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**Theorem 1 of the artifact.**  Let `A` be separable, unital, exact and
quasidiagonal.  Write `T_qd(A)` for its quasidiagonal tracial states, and
`r_A: T(A) -> R^(K_0(A))` for the map `tau -> tau_*`, with
`tau_*(x) = (Tr tensor tau)(x)`.  The following are equivalent.

- (a) Some `x in K_0(A)` with `Zx cap K_0^+(A) = {0}` has `tau_*(x) > 0` for
  every `tau in T_qd(A)`.
- (b) Some `y in K_0(A)` and `sigma in T(A)` satisfy `tau_*(y) > 0` for every
  `tau in T_qd(A)`, and `sigma_*(y) < 0`.
- (c) `r_A(T(A)) != r_A(T_qd(A))`.

Moreover, `sigma` in (b) can be chosen extreme in `T(A)` with
`pi_sigma(A)''` a II_1 factor, which is the hyperfinite II_1 factor `R` when
`A` is nuclear.

Remarks recorded in the artifact.  They are context, not part of the
statement certified by this node's route: the K_0-state form uses the
established `blackadar-rordam-haagerup-k0-states-are-traces` and the
matrix-model form uses `(V1)` of the stw07 artifact, but the UCT remark rests
on Gabe's theorem, which is not a graph node.

- **K_0-state form** (Remark 2.1).  With
  `blackadar-rordam-haagerup-k0-states-are-traces`, `r_A(T(A))` is the whole
  state space of `(K_0(A), K_0^+(A), [1])`.  So the hole
  `qd-nuclear-algebra-with-qd-trace-positive-singular-class` asks for a
  separable unital nuclear quasidiagonal algebra in which the K_0-states
  induced by quasidiagonal traces form a proper subset of the K_0-state space.
- **Matrix-model form** (Remark 2.2).  `r_A(T_qd(A))` is the set of pointwise
  limits of the normalised K_0-maps `(phi_n)_*/k_n` along unital matrix models
  `phi_n: A -> M_(k_n)`.
- **UCT** (Remark 2.3).  With Gabe's theorem (arXiv:1511.02760v1: amenable
  traces on separable exact quasidiagonal UCT algebras are quasidiagonal), an
  algebra satisfying (a) and nuclear does not itself satisfy the UCT.  This
  consequence uses that literature input.  The equivalence above does not.

Proof: route `qd-trace-positive-class-iff-k0-state-off-qd-traces-proof`.
