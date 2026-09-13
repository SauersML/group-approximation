---
rg: 2
id: rational-character-approximable-groups-obey-determinant
kind: claim
title: A group approximable by finite groups through representations with rational characters satisfies the determinant conjecture and Galois balance of eigenvalues
distinct_from:
  determinant-conjecture-holds-for-sofic-groups: that uses permutation models; this uses finite groups through any rational representation, which contains the permutation case and is not known to be larger
  hilbert-embeddable-length-hyperlinearity: that turns Hilbert embeddable finite-group witnesses into hyperlinearity; this restricts to rational characters and obtains the determinant conjecture, which hyperlinearity is not known to give
  integral-eigenvalues-galois-balanced-for-sofic-groups: that is Thom's sofic eigenvalue theorem; this derives the same balance for rational-character approximable groups from the characterization of integer-matrix spectral limits
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

**ESTABLISHED** by `rational-character-approximation-determinant-proof`.
Unreviewed.

**Definition.** Call `G` *rational-character approximable* if for every finite
symmetric `S` containing `e` in `G` and every `eps > 0` there are:
- a finite group `F`;
- a representation `rho : F -> GL_d(Q)`, unitary for an `F`-invariant positive
  definite form `q`;
- a map `phi : S -> F` with `phi(e) = e` and `phi(s^-1) = phi(s)^-1`;

such that, in the normalized Hilbert--Schmidt norm of `q`,

```text
||rho phi(s) rho phi(t) - rho phi(st)||_2 <= eps     (s, t, st in S),
|(1/d) Tr rho phi(s)| <= eps                          (s in S, s != e).
```

Sofic groups qualify: take permutation representations.

**Theorem.** If `G` is rational-character approximable, then for every
self-adjoint `A in M_n(Z[G])` the spectral measure `mu_A` is a limit of
eigenvalue distributions of integer matrices with real spectrum. Consequently:
- `G` satisfies Lück's determinant conjecture;
- every eigenvalue of `A` is a totally real algebraic integer with equal
  conjugate multiplicities
  (`integer-root-limits-are-galois-balanced-serre-measures`).

**Scope.** These models are approximations by the finite subgroups `rho(F)` of
unitary groups. The Kun--Thom wreath admits no such approximation
(`kun-thom-wreath-is-not-rational-character-approximable`). No group is known to
be rational-character approximable and not sofic.
