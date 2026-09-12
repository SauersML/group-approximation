---
rg: 2
id: determinant-conjecture
kind: claim
title: Every group satisfies Lück's determinant conjecture over the integral group ring
root: true
refuted_by:
  - determinant-conjecture-counterexample-exists
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

**OPEN.** For every group `G`, every `m,n`, and every matrix
`A in M_{m x n}(Z[G])`, the Fuglede--Kadison determinant of right
multiplication by `A` on `l^2(G)^m` satisfies `det_N(G)(A) >= 1`
(Lück, *L^2-Invariants*, 2002, Chapter 13).

The conjecture makes L^2-torsion well defined and feeds approximation
theorems for L^2-Betti numbers. It holds for sofic groups
(`determinant-conjecture-holds-for-sofic-groups`, Elek--Szabó 2005). Now that
nonsofic groups exist (`openai-leavitt-unit-nonsofic`), that proof no longer
covers every group (`nonsoficity-blocks-sofic-determinant-transfer`), and a
counterexample, if one exists, must live on a nonsofic group
(`determinant-conjecture-counterexample-exists`).

Structural fact proved here: `determinant-conjecture-iff-serre-class-spectra`.
A group satisfies the conjecture exactly when every self-adjoint element of
`M_n(Z[G])` has a spectral measure obeying every Serre inequality
`integral_{Q!=0} log|Q| d mu >= 0`, for all nonzero `Q in Z[x]`.

## Attempts

- **Soficity of every group.** Dead: some group is not sofic
  (`determinant-conjecture-via-soficity-of-every-group`).
- **Integrality of trace moments.** Dead: an explicit probability measure
  with all moments integers has negative log determinant
  (`integer-moment-measure-with-negative-log-determinant`).
- **One-variable integral approximation.** Live route
  `determinant-conjecture-via-integral-spectral-approximation`: it suffices
  that every integral group-ring spectrum is a weak limit of eigenvalue
  distributions of symmetric integer matrices. This asks nothing about
  approximating `G` itself. The prerequisite is open for every nonsofic group.
