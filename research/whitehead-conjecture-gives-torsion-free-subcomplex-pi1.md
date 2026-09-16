---
rg: 2
id: whitehead-conjecture-gives-torsion-free-subcomplex-pi1
kind: route
title: Under Whitehead's conjecture a finite subcomplex of a contractible 2-complex is a 2-dimensional classifying space, so its group is torsion-free
target: contractible-2-complex-subcomplexes-have-torsion-free-pi1
requires:
  - whitehead-asphericity-conjecture
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

Let `Y` be a contractible 2-dimensional CW complex and `K ⊆ Y` a finite connected subcomplex.

**Step 1: asphericity.**
- `Y` is contractible, hence aspherical.
- By `whitehead-asphericity-conjecture` ("every connected subcomplex of an aspherical 2-complex is
  aspherical"), `K` is aspherical.
- So `K` is a 2-dimensional `K(π_1(K), 1)`, and `cd π_1(K) ≤ 2`.

**Step 2: no torsion.** Recalled standard, not pinned.
- Cohomological dimension does not increase on passing to subgroups.
- `H^n(Z/p; F_p) ≠ 0` for every `n ≥ 0` and every prime `p`, so `cd Z/p = ∞`.
- A nontrivial torsion element has a power of prime order, which would generate a subgroup
  `Z/p ⊆ π_1(K)` with `∞ = cd Z/p ≤ cd π_1(K) ≤ 2`. This is impossible.
- Hence `π_1(K)` is torsion-free.
