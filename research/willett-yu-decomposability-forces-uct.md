---
rg: 2
id: willett-yu-decomposability-forces-uct
kind: claim
title: Decomposability over nuclear UCT algebras forces the UCT, and complexity rank one of trivial-K Kirchberg algebras is equivalent to Problem II
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the open problem; this is the proved Willett--Yu sufficient condition and the equivalence it yields with complexity rank one of trivial-K-theory Kirchberg algebras.
  kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras: that identifies the test class; this supplies a local, finite-dimensional criterion for the UCT on it.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (literature).**  Willett--Yu, *The UCT for C\*-algebras with
finite complexity*, arXiv:2104.10766v4 (Memoirs EMS, forthcoming), Theorem 1.2:
if a separable unital C\*-algebra `A` decomposes over the class of separable
nuclear C\*-algebras satisfying the UCT, then `A` is nuclear and satisfies the
UCT.

Decomposability over a class `C` (Willett--Yu Definition 1.1): for every finite
subset `X` of the unit ball of `A` and every `ε > 0` there are C\*-subalgebras
`C`, `D`, `E` of `A` from `C`, all containing `1_A`, and a positive
contraction `h ∈ E` with

```text
||[h, x]|| < ε,   hx ∈_ε C,   (1 − h)x ∈_ε D,   h(1 − h)x ∈_ε E   (x ∈ X),
every e in the unit ball of E lies within ε of both C and D.
```

Moreover (Jaime--Willett, *Complexity rank for C\*-algebras*, arXiv:2205.04704v2,
Theorem 1.2, second part), all nuclear C\*-algebras satisfy the UCT if and only
if every unital Kirchberg algebra with zero K-theory decomposes over the class
of finite-dimensional C\*-algebras, i.e. has complexity rank at most one.
