---
rg: 2
id: principal-ideal-affine-groups-are-self-similar
kind: claim
title: Affine groups R^n x| Γ over a ring with a finite-index principal left ideal x R-adically separated are self-similar
distinct_from:
  affine-self-similar-coordinate-rings-are-one-dimensional: that is an obstruction showing the ring hypothesis forces transcendence degree zero for commutative domains of characteristic zero; this is the positive criterion itself, for every ring and every subgroup of GL_n(R).
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's rational linear theorem, one application of this criterion with R = Z[1/m]; this is the criterion, which also applies to S-integers of global function fields.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED (literature import, with a routine subgroup check).**

**Hypotheses.** Let `R` be a unital ring and `x in R` such that:
- the principal left ideal `J = Rx` has finite index in `(R, +)`;
- `x` is not a zero divisor;
- `∩_(k in N) R x^k = {0}`.

**Conclusion.** For every `n >= 1` and every subgroup `Γ <= GL_n(R)`, the affine
group `R^n x| Γ` is self-similar. It acts faithfully and self-similarly on the
rooted `d`-regular tree with `d = [R^n : J^n]`.

**Source.** Zaremsky, arXiv:2405.09722, Example 4.7 with Corollary 4.5, for
`Γ = GL_n(R)`.
- *The virtual endomorphism.* `φ: J^n -> R^n` sends `(r_i x)` to `(r_i)`. It is
  surjective and proper.
- *Stability.* `φ` and `GL_n(R)` are mutually stable, because right scaling by
  `x` commutes with left multiplication by matrices.

**The subgroup check.** The same computation gives `φ γ φ^-1 = γ` for every
`γ in Γ <= GL_n(R)`. So `φ` and `Γ` are mutually stable, and Corollary 4.5
applies to `R^n x| Γ` directly.

For commutative Noetherian domains, Zaremsky notes that the intersection
condition holds for every proper `J`, by the Krull intersection theorem.

See `principal-ideal-affine-groups-are-self-similar-citation`.
