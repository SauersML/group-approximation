---
rg: 2
id: group-double-surjunctivity-from-free-kernel
kind: route
title: Identify the double as a free kernel semidirect product and apply the finitary permanence theorem
target: doubles-of-surjunctive-groups-are-surjunctive
requires: [finitary-split-extension-surjunctivity-permanence]
artifacts:
  - research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Lemma 5.1 of the linked artifact identifies `G *_Gamma G` with
`F(X \ {x_0}) semidirect_alpha G`, `alpha_g(e_x) = e_(gx) e_(gx_0)^-1`, by
explicit mutually inverse homomorphisms. Section (I2) verifies the axioms of
`finitary-split-extension-surjunctivity-permanence`:

* (A1): free groups are residually finite, and a word survives once `S`
  contains its letters;
* (A2): letter supports translate under `alpha`;
* (A3): pointwise stabilizers of `S` preserve `X\S`.

The converse is subgroup heredity.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 3 of
the verification artifact).
