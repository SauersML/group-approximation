---
rg: 2
id: separable-finite-algebras-have-symmetry-bases
kind: claim
title: Every separable diffuse finite von Neumann algebra has an orthonormal basis of symmetries
distinct_from:
  non-ru-bcs-is-satisfiable-in-a-group-factor: that asks for a non-CE algebra inside a canonical group factor; this supplies a unitary Hilbert-space basis inside the algebra itself, without multiplicative closure or a regular group trace.
  group-basis-actions-have-permutation-koopman-spectrum: that gives a necessary spectral condition when a basis is already indexed and permuted by a group action; this supplies no permutation or multiplication law on its basis.
artifacts:
  - research/artifacts/kadison-symmetry-basis-groupification-audit-2026-08-21.md
---

He--Tang--Zhang, arXiv:2605.15006v2, Theorem 1, prove:

> If `(M,tau)` is a diffuse finite von Neumann algebra, `tau` is faithful and
> normal, and `L^2(M,tau)` is separable, then `L^2(M,tau)` has an orthonormal
> basis consisting of symmetries `s=s^*=s^(-1)` in `M`.

In particular this applies to every separable non-Connes-embeddable factor
used by the programme.  The theorem solves the old separable Kadison
trace-vector basis problem, but it does not make `M` a group factor: the
basis is produced by a greedy finite-orthogonality construction and is not
closed under multiplication.

The exact groupification boundary is
`projectively-closed-symmetry-bases-are-hyperfinite`.
