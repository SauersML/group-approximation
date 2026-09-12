---
rg: 2
id: radu-bmw-no-invariant-output-automata-proof
kind: route
title: Finite quotients see output symmetry, and every involution of Radu's lattice survives abelianization
target: radu-bmw-lattice-has-no-invariant-output-injective-automata
requires:
  - invariant-output-injective-ca-need-torsion
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

Section 1 of the artifact.

1. `invariant-output-injective-ca-need-torsion` makes `H` finite.
2. For any finite-index normal subgroup `N`, injectivity on the `|A|^([G:N])` configurations constant
   on the cosets of `N` forces `H <= N` (Theorem 1, step 2).
3. The citation claim gives the simply transitive action on `T_3 x T_3` with the letters as edge
   inversions at the base vertex. So an involution fixes a point in an edge or a square, and it is
   conjugate to a letter or to a half-turn `hv` of a commuting square: `ax`, `ay` or `bx`.
4. The presentation gives `Gamma_R^ab = (Z/2)^3` on the images of `a, x, y`. All nine involution types
   map to nonzero vectors, so a nontrivial finite `H` is not inside `[Gamma_R, Gamma_R]`, which has
   index eight. Hence `H = 1`.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently: the `Fix_N` count
`|A|^[G:N] <= |A|^[G:HN]`, the classification of involutions (edge inversions, and half-turns `hv`
with `hv = vh`), and `Gamma_R^ab = (Z/2)^3` with all nine images nonzero
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 5.2).
