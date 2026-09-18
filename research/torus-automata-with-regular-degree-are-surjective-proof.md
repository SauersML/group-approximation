---
rg: 2
id: torus-automata-with-regular-degree-are-surjective-proof
kind: route
title: Pick a nonzero minor on a finite window, read it as the degree of a slice map between tori, and pass to the limit by compactness
target: torus-automata-with-regular-degree-are-surjective
requires: []
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

Section 1 of the artifact (Theorem 1). Two standard facts are used.

- **(F1)** Maps between tori are classified up to homotopy by their `H^1` matrix. The
  degree of a map between tori of equal dimension is the determinant of that matrix.
- **(F2)** A map of nonzero degree between closed connected oriented manifolds of equal
  dimension is surjective.

**Proof.**
1. *A nonzero minor.* Fix a finite `F in G` and put `R = F x {1..d}`. The rows
   `e_(h,i) D`, `(h,i) in R`, are independent over `Q` and supported in the finite set
   `R' = (F . supp D) x {1..d}`. So some `R x S` minor, with `S in R'` and `|S| = |R|`,
   is nonzero.
2. *A slice map.* Freeze the input coordinates outside `S` at an arbitrary configuration.
   This gives `phi: T^S -> T^R`, `x -> tau(x)|_F`. By naturality of `H^1`, `phi` has
   `H^1` matrix equal to the minor, so `deg phi != 0` by (F1), and `phi` is onto by (F2).
3. *Compactness.* Every pattern on `F` is attained, so `tau(X)` is dense. It is compact,
   hence closed, hence everything.
