---
rg: 2
id: aperiodic-subshift-ring-ideals-are-invariant-open-sets
kind: claim
title: Every ideal of LC(X,F_2) ⋊ Z, for a subshift X without periodic points, is the ideal of an invariant open set
distinct_from:
  steinberg-algebra-simple-iff-minimal-effective: that is simplicity of Steinberg algebras (the minimal case); this classifies all two-sided ideals of the crossed product of a non-minimal aperiodic subshift
artifacts:
  - research/artifacts/sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `aperiodic-subshift-ring-ideals-are-invariant-open-sets-proof`.

Let X ⊆ A^Z be a subshift without periodic points and R = LC(X,F_2) ⋊ Z.
- Every two-sided ideal J of R equals `I_U = {Σ f_j u^j : supp f_j ⊆ U}` for exactly one invariant open U ⊆ X, namely U = ⋃{V clopen : e_V ∈ J}.
- Restriction gives R / I_U ≅ LC(Y,F_2) ⋊ Z, with Y = X ∖ U.

So the lattice of ideals of R is the lattice of subsystems of X, reversed. Compare the ideal theory of Steinberg algebras (Clark–Edie-Michell; Steinberg). The proof here is direct.
