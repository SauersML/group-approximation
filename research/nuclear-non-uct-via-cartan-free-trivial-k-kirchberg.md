---
rg: 2
id: nuclear-non-uct-via-cartan-free-trivial-k-kirchberg
kind: route
title: A unital trivial-K-theory Kirchberg algebra without a Cartan subalgebra is a UCT counterexample
target: nuclear-algebra-without-uct-exists
requires: [uct-cartan-trivial-k-kirchberg-without-cartan-exists, uct-cartan-trivial-k-kirchberg-uct-iff-cartan]
artifacts:
  - research/artifacts/uct-cartan-obstruction-2026-09-12.md
---

Let `A` be a unital Kirchberg algebra with trivial K-theory and no Cartan
subalgebra (`uct-cartan-trivial-k-kirchberg-without-cartan-exists`).  `A` is
separable and nuclear, and by 1 ⟹ 3 of
`uct-cartan-trivial-k-kirchberg-uct-iff-cartan` it does not satisfy the UCT.  So
`A` witnesses `nuclear-algebra-without-uct-exists`.  The same node shows the
converse, so this certificate shape loses nothing.
