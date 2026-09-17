---
rg: 2
id: whitehead-asphericity-conjecture
kind: claim
title: Every connected subcomplex of an aspherical 2-complex is aspherical
root: true
distinct_from:
  eilenberg-ganea-conjecture: that concerns the geometric dimension of groups of cohomological dimension 2; this concerns subcomplexes of aspherical 2-complexes.
  nonaspherical-subcomplex-of-contractible-2-complex-exists: that is a counterexample statement, which refutes this conjecture if established.
refuted_by:
  - nonaspherical-subcomplex-of-contractible-2-complex-exists
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**OPEN.** Whitehead's asphericity conjecture, in the form recalled by
Bestvina--Brady (Invent. Math. 129 (1997), p. 461, read from the Springer PDF
on MSI): "The Whitehead conjecture states that every connected subcomplex of an
aspherical 2-complex is aspherical."

**Links.** `eilenberg-ganea-or-whitehead-is-false` (Bestvina--Brady
Theorem 8.7): this conjecture or `eilenberg-ganea-conjecture` is false.

## Attempts

1. **Bestvina--Brady kernels (2026-09-13).** For every finite flag 2-complex
   `L` that is acyclic but not aspherical,
   `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead` shows that a
   2-dimensional `K(H_L,1)` produces a finite connected non-aspherical
   subcomplex of a contractible 2-complex. For the Poincaré-sphere spine this
   is the route `nonaspherical-subcomplex-via-bestvina-brady-kernel`, waiting
   on `bestvina-brady-poincare-kernel-has-geometric-dimension-two`. Undecided.

2. **Pasku's one-relator deletion proof (arXiv:2107.12293v1), 2026-09-17.**
   `pasku-whitehead-proof-gap-relative-exactness-lemma` audits the claimed
   proof at source level. The key relative exactness Lemma `c-rel-ext` applies
   Kobayashi--Otto Theorem 6.6 with the ideal of the trivial group instead of
   `J_1 = ker(ZF → ZG_1)`, and the inference fails for `⟨x,y | x,y⟩` minus `y`.
   The lemma by itself already implies the claimed theorem whenever `G_1 ≠ 1`,
   and it is valid only when `G_1 = 1`, where the theorem is trivial. So the
   paper is not an input to this conjecture, and the Ivanov route stays open.

3. **Sylvester rank specialization (2026-09-17).** For a one-cell complement `K = L − e`, `K` is
   aspherical once the square Fox matrix `M` (the relators of `K` plus the boundary word of `e`) has
   full von Neumann rank. `ε(M)` is always unimodular. A single rank comparison `rk_G ≥ rk'` with
   `rk'(M)` full would prove this. `rank-specialization-one-cell-asphericity-only-locally-indicable`
   shows that such a comparison forces the subgroup killed by `rk'` to be locally indicable. So the
   augmentation, abelian characters, locally indicable quotients and universal localization reach
   only Howie's locally indicable class. The Hantzsche--Wendt group and hyperbolic homology spheres
   break dominance explicitly. Dominance transfer across a locally indicable normal subgroup `N`
   is dead as well. Its hypothesis `rk_{G/N}(πM) = g` gives `H₂` of the cover `K_N` equal to 0, so
   Howie applies to `K_N` directly. Still alive: non-faithful rank functions and approximation
   arguments. Obstruction, not a resolution.
