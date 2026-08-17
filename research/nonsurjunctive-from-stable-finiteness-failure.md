---
rg: 2
id: nonsurjunctive-from-stable-finiteness-failure
kind: route
title: Feed a one-sided inverse over F_2 into the linear-automaton criterion
target: leavitt-unit-group-nonsurjunctive
requires: [stable-finiteness-failure-refutes-surjunctivity, leavitt-group-algebra-not-stably-finite]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

`stable-finiteness-failure-refutes-surjunctivity` is stated for an arbitrary
group and an arbitrary finite field.  Instantiate it at `k = F_2` and
`G = L_(F_2)(1,2)^x`; the matrices supplied by
`leavitt-group-algebra-not-stably-finite` are exactly its hypothesis.  The
conclusion is an injective non-surjective linear cellular automaton on the
full shift over the finite alphabet `F_2^n`, which is the target.

This is the **only** live route to the target in this graph.  The dynamical
material the repository already owns — the strict self-embedding of the
proper subshift `X` — cannot substitute for it; see
`subshift-self-embedding-carries-no-surjunctivity-content`.

The reduction is not a restatement: the target quantifies over all finite
alphabets and all cellular automata, including nonlinear ones, while the
prerequisite is a purely algebraic statement about one group algebra.  A
proof of the target need not go through it — a nonlinear construction would
bypass group-ring finiteness entirely — so this route is a genuine narrowing
and not the only conceivable one.
