---
rg: 2
id: determinant-conjecture-counterexample-exists
kind: claim
title: Some group has an integral group-ring matrix with Fuglede--Kadison determinant below one
root: true
distinct_from:
  determinant-conjecture: that is the universal positive statement; this asks for one violating group and matrix, which would refute it
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**OPEN.** Exhibit a group `G` and `A in M_{m x n}(Z[G])` with
`det_N(G)(A) < 1`. This would refute Lück's determinant conjecture.

**Necessary shape.**
- `G` must be nonsofic (`determinant-conjecture-holds-for-sofic-groups`).
- By `determinant-conjecture-iff-serre-class-spectra`, one self-adjoint
  `A in M_n(Z[G])` and one nonzero `Q in Z[x]` must satisfy
  `integral_{Q!=0} log|Q| d mu_A < 0`.
- The model failure is `integer-moment-measure-with-negative-log-determinant`:
  conjugate algebraic eigenvalues carrying unequal von Neumann multiplicity,
  with no continuous part compensating.
- **The violating self-adjoint matrix must have infinite spectrum.** Over every
  group, finite-spectrum integral matrices have rational, Galois-equal masses
  and satisfy every Serre inequality
  (`finite-spectrum-integral-elements-obey-determinant`, via Zalesskii's
  theorem). So the model failure above cannot occur with finitely many atoms.

## Attempts

- **Test groups.** The binary Leavitt unit group
  (`openai-leavitt-unit-nonsofic`), the Kun--Thom wreaths
  (`kun-thom-nonsofic-wreath`), and Fournier-Facio's torsion-free group
  (`fournier-facio-group-is-nonsofic`). No candidate matrix has been proposed
  yet.
- **Kun--Thom wreath through finite quotients.** `L(W)` is the generalized
  Bernoulli crossed product, whose action is not sofic. The finite quotients
  obtained by summing over fibers of `G/Gamma -> G/(Gamma N)` approximate a
  proper quotient trace, not `mu_A`, because `Gamma` is not profinitely
  closed. So they certify neither side. A violation would have to live on the
  part of the spectrum that the profinite shadow does not see.
- **Galois-unequal multiplicities with finite spectrum.** Dead for every
  group. A self-adjoint `A` with atoms at `phi^2` and `phi^-2` carrying unequal
  multiplicity and no other spectrum would violate the conjecture. But its
  spectral projections are polynomials in `A` over `Q(sqrt 5)`, so they lie in
  the group algebra, and Zalesskii's theorem makes their traces rational, hence
  equal on conjugates (`finite-spectrum-integral-elements-obey-determinant`).
  This kills `determinant-counterexample-via-galois-unequal-atoms`.
- **Galois-unequal multiplicities with infinite spectrum.** Open. An isolated
  algebraic atom has its projection in `C*_r(G)`, not in `K[G]`, so neither
  Zalesskii nor soficity controls its trace. Galois invariance of
  L^2-multiplicity is known for sofic groups
  (`vn-rank-galois-invariant-for-torsion-free-groups` records the torsion-free
  question). Unequal atoms alone do not violate the conjecture; the rest of the
  spectrum must not compensate.
