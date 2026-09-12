---
rg: 2
id: function-field-borel-groups-are-fp-for-three-places
kind: claim
title: Borel subgroups of general linear groups over S-integers of a global function field are finitely presented once S has three places
distinct_from:
  function-field-soluble-groups-embed-in-fp-self-similar-groups: that consumes finite presentation of affine Borel groups to build self-similar envelopes; this is the finiteness theorem for the Borel groups themselves.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `K` be a global function field, `S` a
finite set of places of `K` with `|S| >= 3`, and `O_S` the ring of `S`-integers.
For every `n >= 1`, the group `B_n(O_S)` of invertible upper triangular
`n x n` matrices over `O_S` is finitely presented.

**Source.** K.-U. Bux, *Finiteness properties of soluble arithmetic groups over
global function fields*, Geom. Topol. 8 (2004), arXiv:math/0212365. Theorem A,
read from the arXiv TeX source on MSI
(`/scratch.global/sauer354/bhmeta/src-math_0212365/2004-15.tex`), verbatim up to
macros: "Let G be a Chevalley group, B ≤ G a Borel subgroup, K a global function
field, S a non-empty set of places over K, and O_S the corresponding
S-arithmetic ring. Then B(O_S) is of type F_{|S|-1} but not of type FP_{|S|}."
The paper fixes "a Chevalley group G, ie, a semisimple linear algebraic group
defined over Z".

**From SL to GL.** Theorem A applies to `SL_n`, which is semisimple, and not
directly to `GL_n`. The routine deduction is in
`function-field-borel-groups-are-fp-for-three-places-citation`.
