---
rg: 2
id: lcs-construct-weighted-conjugacy-to-lcs
kind: claim
title: Weighted linear-plus-conjugacy energy lowers to binary LCS with perfect quantum completeness and a uniform explicit gap
distinct_from:
  wagon-wheel-stops-before-bcs-groupification: That gives a fixed-word restriction bound and identifies the preceding nonaffine BCS gate; this supplies a weighted polynomial-size lowering for the restricted linear-plus-conjugacy language, including approximate completeness and uniform game soundness.
  finite-linear-commutation-system-to-lcs: That lowers linear rows and selected commutations at exact satisfiability; this also lowers arbitrary involutory conjugacy requirements with a weighted dimension-independent error bound.
  lcs-perfect-quantum-completeness-re-hardness: That asks for a HALT-positive machine family; this completes the last lowering conditional on such a family already existing in the specified restricted word language.
artifacts:
  - research/artifacts/lcs-constructive-compiler-2026-09-20.md
---

Fix k>=1. Consider a finite instance with self-adjoint involution variables,
positive rational requirement weights summing to one, linear rows of
distinct variables with width 1<=l<=k, and conjugacy requirements
X_i X_j X_i=X_h. Define the energy
of a linear row to be one quarter the squared normalized-HS parity-product
defect plus one quarter the sum of squared additive commutator defects over
its unordered variable pairs. Define conjugacy energy to be one quarter
||X_i X_j X_i-X_h||_2^2. Let e_* be the infimum of the weighted total energy
over all matrix dimensions and involution tuples.

There is a polynomial-time transformation of the explicit weighted instance
to a finite binary LCS L with rational row weights and maximum row width
K=max(k,3), such that:

- e_*=0 implies omega_q(L)=omega_qa(L)=1.
- An exact source solution in dimension d extends to an exact output
  operator solution in dimension 4d.
- If e_*>=Delta>0, then

```
omega_q(L) <= 1 - (Delta/(148 C_k))^4/K,
C_k=max(9k^2,14652).
```

The game samples a row by its prescribed weight, then a uniformly random
variable in that row. Each source linear row is retained with its weight;
each source conjugacy is replaced by 22 rows, sharing its weight equally.
Constants do not depend on source size, minimum row weight, or dimension.

The gadgets are Slofstra's restricted linear-plus-conjugacy embedding;
the arbitrary-quantum rounding input is Culf's 2026 Corollary 7.3. The
artifact proves the weighted decoder and the displayed constants.
This establishes no machine-indexed source family, no general nonaffine
BCS compiler, and no perfect-completeness RE-hardness theorem.
