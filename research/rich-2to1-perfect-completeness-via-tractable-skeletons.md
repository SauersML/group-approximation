---
rg: 2
id: rich-2to1-perfect-completeness-via-tractable-skeletons
kind: route
title: Dead -- obtain perfect-completeness rich 2-to-1 hardness by right-merging satisfiable unique games, certified affine-local wrapping, or an affine F_lin-stage start of the enrichment chain
target: rich-2to1-perfect-completeness-conjecture
requires: []
---

**Dead.** This route runs one of the three known rich-producing constructions
with perfect completeness:

* run BKM Theorem 8's direction from unique games (the right merge `Psi(U)`, or
  partial merges);
* wrap a proved 2-to-1 instance with locally complete right vertices over affine
  intended classes, with certified completeness;
* start BKM's floated chain `F_0 = F_lin ⊆ F_1 ⊆ ... ⊆ F_T = F_all` from an
  `F_lin`-rich stage with perfect completeness and affine constraints.

It is killed by `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p`.
Each construction leaves a skeleton of mass `> delta` that can be computed from
the reduction's run: a one-seed forcing closure, a satisfiable unique game
`U_W(G)`, or a linear system. Perfect completeness makes the skeleton
satisfiable, and its search problem is polynomial. So the source language is in
P.

The kill is at completeness exactly 1. The same constructions at completeness
`1 - eps` are the live imperfect-completeness region of
`rich-2to1-games-conjecture`.
