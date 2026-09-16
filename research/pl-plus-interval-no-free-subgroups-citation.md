---
rg: 2
id: pl-plus-interval-no-free-subgroups-citation
kind: route
title: Import Brin–Squier and Monod on free subgroups of piecewise linear and projective groups of the line
target: pl-plus-interval-has-no-non-abelian-free-subgroups
requires: []
---

Literature import. It was recorded on 2026-09-16 by the referee of the swarm lane
`zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f`.

## Sources

1. **M. G. Brin and C. C. Squier**, *Groups of piecewise linear homeomorphisms of the real
   line*, Invent. Math. 79(3) (1985) 485–498, DOI 10.1007/BF01388519. The bibliographic
   data was checked against Crossref on 2026-09-16. The paper itself was not fetched
   (Springer login redirect). Its main theorem, that the group of piecewise linear
   homeomorphisms of the line with finitely many breakpoints contains no non-abelian
   free subgroup, is the classical fact already imported for `F` in
   `thompson-f-no-free-subgroups-citation`.
2. **N. Monod**, *Groups of piecewise projective homeomorphisms*, Proc. Natl. Acad. Sci.
   USA 110(12) (2013) 4524–4527, DOI 10.1073/pnas.1218426110, arXiv:1209.5229. The TeX
   source was fetched on 2026-09-16.
   - `G` is defined there as the group of all homeomorphisms of `P^1(R)` that are
     piecewise in `PSL_2(R)`, with finitely many pieces, each an interval of `P^1`.
     `H < G` is the stabiliser of `∞`.
   - Monod states: "The next result is a sequacious generalization of the corresponding
     theorem of Brin--Squier about piecewise affine transformations" and then the
     theorem: "The group $H$ does not contain any non-abelian free subgroup."
   - He sketches the proof, following Brin–Squier Theorem 3.2 (page 495 there) and
     Cannon–Floyd–Parry p. 232.

## What is imported, and why it covers PL_+([0,1])

Only the statement that `H` has no non-abelian free subgroup. Here is why `PL_+([0,1])`
is a subgroup of `H`.

- Extend `f` in `PL_+([0,1])` by the identity on `R \ [0,1]`, and let it fix `∞`.
- Every affine map `x ↦ a x + b` with `a > 0` is the Möbius map of the matrix
  `[[√a, b/√a], [0, 1/√a]]` in `SL_2(R)`, and it fixes `∞`.
- So the extension is piecewise in `PSL_2(R)`, with finitely many pieces:
  - the linear pieces of `f`;
  - the single interval `[1, ∞] ∪ [−∞, 0]` of `P^1` through `∞`, where it is the
    identity.
- The extension map is an injective homomorphism into `H`.

Subgroups of groups without non-abelian free subgroups have none.

## Trust boundary

- The proofs were not re-derived.
- Brin–Squier was not fetched, only its bibliographic record.
- Monod's statement and proof sketch were read from the arXiv TeX source.
