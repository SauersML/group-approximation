---
rg: 2
id: labbe-not-fp-via-mean-area-relation-invariant
kind: route
title: DEAD - refute finite presentation of Labbé's derived full group through an invariant-measure area invariant of relations
target: labbe-shift-derived-full-group-is-not-finitely-presented
requires: []
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**Dead route.** It is invalidated by `labbe-shift-derived-full-group-homology-is-finitely-generated`, which is
established.

**Intended argument (relation compression).** The invariant probability `μ` of `Omega_U` makes
conjugation preserve the measure of supports. So fine relations never arise as conjugates of
coarse relators.
- A measure-weighted relation invariant would witness this. An example is
  `alpha(w) = ∫ A(w, x) dμ(x)`, the mean signed area of the closed lattice loop that the orbit of
  `x` traces under a relator `w`.
- Its values on the finitely many relators of a finite presentation generate `alpha(N)`. So an
  infinitely generated `alpha(N)` would refute finite presentation.

**Why it dies.** `alpha` is additive on `N`, and invariant under conjugation by the free group
because `μ` is invariant. So it factors through `N/[F,N]`.
- By Hopf's formula, `N/[F,N]` is an extension of a subgroup of `Z^{|S|}` by `H_2(Gamma)`.
- `H_2(Gamma)` is finitely generated, so the image of every conjugation-invariant homomorphism
  on `N` is finitely generated.
- Part 1 of the artifact, Proposition 5, has the argument.
