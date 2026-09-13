---
rg: 2
id: integral-group-ring-eigenvalues-are-galois-balanced
kind: claim
title: Over every group the eigenvalues of integral self-adjoint matrices are totally real algebraic integers with equal conjugate multiplicities
distinct_from:
  galois-invariance-forces-totally-real-atoms: that derives total reality and balance from invariance of kernel dimensions for all algebraic matrices over a given group; this asserts the balanced integral shape for integral self-adjoint matrices over every group, with no invariance hypothesis
  heavy-eigenvalue-gives-determinant-counterexample: that shows the determinant conjecture forces algebraic eigenvalues of multiplicity at most n over the degree; this asks for integrality and exact balance, which the conjecture does not force one measure at a time
  vn-rank-galois-invariant-for-torsion-free-groups: that is invariance under automorphisms of C fixing Qbar, over torsion-free groups; this concerns the action of Gal(Qbar/Q) on eigenvalues of integral matrices, over all groups
artifacts:
  - research/artifacts/determinant-integer-root-limits-2026-09-12.md
---

**OPEN.** For every group `G`, every self-adjoint `A in M_n(Z[G])` and every
eigenvalue `lambda` of `r_A` on `l^2(G)^n`:
- `lambda` is a totally real algebraic integer;
- `dim_(N(G)) ker(r_A - sigma lambda) = dim_(N(G)) ker(r_A - lambda)` for every
  `sigma in Gal(Qbar/Q)`.

This is the self-adjoint integral case of the algebraic eigenvalue conjecture of
Dodziuk--Linnell--Mathai--Schick--Yates (Conjecture 4.14 of their CPAM 56 paper,
as cited by Thom).

**Place in the graph.**
- **Equivalence.** With `determinant-conjecture`, it is equivalent to
  `integral-group-ring-spectra-are-integer-root-limits`
  (`integer-root-limits-are-galois-balanced-serre-measures`, artifact
  Section 4).
- **Sofic groups:** holds (`integral-eigenvalues-galois-balanced-for-sofic-groups`).
- **Finite spectrum, any group:** holds
  (`finite-spectrum-integral-elements-obey-determinant`, via Zalesskii).
- **The determinant conjecture gives only part of it.** It forces algebraic
  eigenvalues of multiplicity at most `n / deg`
  (`heavy-eigenvalue-gives-determinant-counterexample`). It does not force
  integrality or balance one measure at a time
  (`serre-class-admits-non-integral-atoms`).

## Attempts

- **From the determinant conjecture.** Only the degree bound follows from the
  Serre inequalities of single measures. Amplifying through `G x G` or
  Kronecker sums multiplies atom ratios, but the continuous part grows and keeps
  compensating. No contradiction found.
- **Integral kernel dimensions cannot see balance.** For `Q in Z[x]`,
  `dim ker r_(Q(A))` is the sum of `dim ker(r_A - beta)` over the roots `beta`
  of `Q`, a sum over whole Galois orbits. The same holds for Kronecker
  combinations `A (x) I - I (x) M` with integer `M`, and for restriction of
  scalars from `O_K[G]`. So no Atiyah-type integrality statement over `Z`
  about the algebra of `A` detects imbalance. Only compensation failures in
  determinants, or kernels over `Qbar[G]`, can.
- **From invariance of kernel dimensions.** `galois-invariance-forces-totally-real-atoms`
  gives total reality and balance, but not integrality, from
  `Gal(Qbar/Q)`-invariance over `Qbar[G]`. That invariance is itself open for
  nonsofic groups.
