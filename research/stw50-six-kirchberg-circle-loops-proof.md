---
rg: 2
id: stw50-six-kirchberg-circle-loops-proof
kind: route
title: Combine four detected edge phases with the two graded tensor-factor actions
target: stw50-six-kirchberg-circle-loops
requires:
  - stw50-kirchberg-loop-classification-inputs
artifacts:
  - research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md
  - experiments/stw50_six_kirchberg_loops_check.py
---

The common initial-projection row construction gives explicit
unitaries U_1,U_2 in C and V in B. Phasing a single edge evaluates
on these unitaries as the Bott loop of its range projection.
The vertex K-classes detect U_1,U_2 and V as integral bases.

Four C edge phases supply the elementary maps K_1 -> K_0. The
inverse edge phase in B sends [V] to [1]. Its two tensor-factor
actions on A send beta=[V] external-product [V] to y and -x.
They therefore supply a basis of the remaining K_0/Z[1] -> K_1
quotient. A fixed unital classification isomorphism places all
six actions on A. The full invariant matrix has determinant 1.
The natural invariant is injective and onto by the prerequisite,
so this proves an integral basis of actual automorphism loops.

The script checks the finite arithmetic; the complete new
mathematical argument is Sections 2--6 of the artifact.
