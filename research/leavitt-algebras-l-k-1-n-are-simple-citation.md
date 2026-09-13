---
rg: 2
id: leavitt-algebras-l-k-1-n-are-simple-citation
kind: route
title: Import the Abrams--Aranda Pino simplicity theorem and apply it to the rose with n petals
target: leavitt-algebras-l-k-1-n-are-simple
requires: []
---

Citation import. Nothing is re-proved here beyond checking the graph conditions.

G. Abrams, *Leavitt path algebras: the first decade*, arXiv:1410.1835v1 (Bull.
Math. Sci., forthcoming at the time). Read on 2026-09-12 from the arXiv PDF,
page 10, by lane `ex-q34-leavitt-hs`:

> **Theorem 1.20. (The Abrams / Aranda Pino Simplicity Theorem)** [7, Theorem 3.11])
> Let E be a finite graph and K any field. Then L_K(E) is simple if and only if
> the only hereditary saturated subsets of E are trivial, and every cycle in E has
> an exit.

Reference [7] of the survey is G. Abrams and G. Aranda Pino, *The Leavitt path
algebra of a graph*, J. Algebra 293 (2005), where the statement is Theorem 3.11.
The survey also recalls, in Example 1.7(3) on page 4, that the Bergman algebra
`B(V_n, x)` "is precisely the Leavitt algebra L_K(1,n)". Its defining relations
are `y_i x_j = delta_(i,j) 1` and `sum_(i=1)^n x_i y_i = 1`.

**Checking the conditions for the rose `R_n`.** `R_n` has one vertex `v` and `n`
loops. A hereditary saturated subset is either empty or contains `v`, so it is
trivial. A cycle in `R_n` is a single loop `e_i`. For `n >= 2` any other loop `e_j`
satisfies `s(e_j) = v = s(e_i)` and `e_j != e_i`, so it is an exit. The Leavitt path
algebra of `R_n` is `L_K(1,n)`, with `x_i = e_i` and `y_i = e_i^*`.
