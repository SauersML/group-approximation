---
rg: 2
id: fp-central-simple-hosts-via-cantor-crossed-products
kind: route
title: Take the host to be a Cantor crossed product by a torsion-free Farrell–Jones group, where the Leavitt-tensor K-theory vanishes automatically
target: decidable-group-algebras-have-fp-central-simple-hosts
requires:
  - decidable-group-algebras-have-fp-cantor-crossed-hosts
  - cantor-crossed-product-leavitt-tensors-are-k-trivial
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

Let `G` be finitely generated with solvable word problem.

1. `decidable-group-algebras-have-fp-cantor-crossed-hosts` gives a torsion-free
   Farrell–Jones group `P`, a nonempty compact totally disconnected `P`-space
   `X`, and `B = LC(X, F_2) ⋊ P`. This `B` is finitely presented, simple, has
   centre `F_2`, and contains `F_2[G]` unitally.
2. `cantor-crossed-product-leavitt-tensors-are-k-trivial`(1) with `k = F_2` gives
   `K_n(B ⊗ L) = 0` for every `n`, in particular for `n = 1, 2`.

That is the statement of `decidable-group-algebras-have-fp-central-simple-hosts`.

**What this route changes.** The target asks for a finitely presented central
simple algebra together with a `K`-theory condition. On this route the
`K`-theory condition is automatic, and what remains is a question about
dynamics: finite presentation, simplicity and a unital embedding of `F_2[G]`.
The hosts need not be coherent (`cantor-crossed-product-leavitt-tensors-are-k-trivial`(2)),
so the obstruction recorded as Attempt 5 on the target does not apply.

The open premise is at least as hard as Boone–Higman, granted the graph's chain
from the target to `boone-higman-conjecture` (conditional on Khanh
arXiv:2609.08428v1 through `leavitt-tensor-hosts-acyclic-steinberg-and-fp`). Attempts on it are
recorded in `decidable-group-algebras-have-fp-cantor-crossed-hosts` and in
Section 7 of the artifact.
