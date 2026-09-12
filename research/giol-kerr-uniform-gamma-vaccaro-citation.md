---
rg: 2
id: giol-kerr-uniform-gamma-vaccaro-citation
kind: route
title: Import Vaccaro's uniform Gamma theorem for free minimal actions of FC groups
target: giol-kerr-crossed-products-have-uniform-gamma
requires: []
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

A. Vaccaro, *Stable rank one, tracial local homogeneity and uniform property
Gamma*, arXiv:2604.24682v2 (revised 2026-05-03).  Read from the PDF text on
MSI, 2026-09-12: pages 1--3 and the end of Section 4.

- **Theorem A(2).** "A crossed product of a free minimal action by a countably
  infinite FC (e.g. abelian) group on a compact metric space" has uniform
  property Gamma.
- **Corollary 4.6.** If a countably infinite amenable group acts freely and
  minimally on a compact metric space with the uniform Rokhlin property, the
  crossed product has uniform property Gamma.
  - The proof combines Niu's tracial local homogeneity for URP crossed products
    (Vaccaro's Theorem 4.5, after Niu arXiv 2022, Theorem 3.9) with Vaccaro's
    Theorem 3.6.
  - Stable rank one is not used.
- The paragraph after Corollary 4.6 derives Theorem A(2) from Naryshkin's
  Corollary E ([Nar24]): every free minimal action of an FC group has the URP.
  Naryshkin was not re-read here.

**Application.**  The Giol--Kerr examples (J. reine angew. Math. 639 (2010))
are crossed products `C(X) rtimes_h Z` by minimal homeomorphisms `h` of an
infinite compact metrizable space `X`.
- A minimal homeomorphism of an infinite compact space has no periodic point,
  since a finite orbit would be a closed invariant proper subset.  So the
  `Z`-action is free.
- `Z` is abelian, hence FC.
- Theorem A(2) applies: every such crossed product, including the
  non-Z-stable Giol--Kerr algebras, has uniform property Gamma.

This bypasses both open prerequisites of the other routes: the Giol--Kerr and
Villadsen tracial-completion identification (STW XXXV), and the finite-stage
flat colouring statement.
