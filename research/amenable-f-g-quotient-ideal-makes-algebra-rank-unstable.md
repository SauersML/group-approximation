---
rg: 2
id: amenable-f-g-quotient-ideal-makes-algebra-rank-unstable
kind: claim
title: A finitely presented algebra with a one-sided finitely generated ideal whose quotient is amenable and has no finite-dimensional representations is not rank-stable
distinct_from:
  free-quotient-obstructs-flexible-uniform-rank-stability: that is Bachner's instability theorem for groups with a free quotient; this is Bauer--Blachar--Greenfeld's instability criterion for algebras, through an amenable quotient without finite-dimensional representations.
  amenable-group-algebra-rank-stability-iff-rf: that is an if-and-only-if for amenable domains in weak stability; this is a one-way obstruction to flexible rank-stability for arbitrary finitely presented algebras.
artifacts:
  - research/artifacts/solve-weakly-sofic-2026-09-13.md
---

**ESTABLISHED (import).** Let `A` be a finitely presented algebra over a field and `I` a nonzero two-sided ideal of
`A`. Suppose:
- `I` is finitely generated as a left ideal of `A`;
- the algebra `A/I` is amenable, in the sense of Elek and Gromov: for every `eps > 0` some finite-dimensional
  subspace `V` has `dim(SV + V) < (1 + eps) dim V`, where `S` is a finite generating set;
- `A/I` has no finite-dimensional representations.

Then `A` is not rank-stable (definition on `fp-group-rank-stability-equals-group-algebra-rank-stability`).

**Mechanism.** Følner subspaces of `A/I` give truncated approximate representations. A nearby exact solution carries
a nonzero subspace killed by the left generators of `I`, and that subspace is an `A/I`-module of finite dimension.

Citation route: `algebra-rank-instability-criterion-citation`.
