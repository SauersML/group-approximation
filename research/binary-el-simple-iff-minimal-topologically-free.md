---
rg: 2
id: binary-el-simple-iff-minimal-topologically-free
kind: claim
title: For n at least 3, EL_n of the binary crossed product of a zero-dimensional action is simple exactly when the action is minimal and topologically free
distinct_from:
  steinberg-elementary-groups-are-simple-mod-centre: that gives simplicity modulo the centre over any field, for every minimal effective ample groupoid, through Steinberg algebra machinery; this is a two-way criterion over F_2, proved by the manuscript's elementary tower argument, and it also computes the centre to be trivial.
  finite-model-subshift-elementary-groups-simple-kazhdan-lef: that assumes the action is free at every point and concludes simplicity together with property (T) and LEF; this weakens the hypothesis to topological freeness, is an equivalence, and claims nothing about LEF.
  subshift-elementary-group-simple-iff-infinite-minimal: that is the equivalence for subshifts over Z, over any field, modulo the centre; this is any countable acting group on any compact zero-dimensional space, over F_2, with the centre shown trivial.
artifacts:
  - research/artifacts/sk-strong-4-boundaries-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let a countable group `Γ` act by homeomorphisms on a compact
Hausdorff zero-dimensional space `X`, let `R = LC(X,F_2) ⋊ Γ`, and let `n ≥ 3`. Then `EL_n(R)` is
simple if and only if the action is minimal and topologically free. When it is,
`Z(EL_n(R)) = 1`, so no quotient is needed.

The forward direction is proved by the manuscript's own tower argument, with `u^j` replaced by
`u_γ`. Freeness is used nowhere. The one step that seems to need it, the decomposition of `X` into
small clopen sets, is replaced by the density statement of
`clopen-towers-at-every-scale-iff-topologically-free`: the small sets cover a dense open subset of
`X`, and a locally constant function vanishing there is `0`.

**Consequences.**
- An action with one dense free orbit is topologically free, since a fixed clopen set would meet
  that orbit. So the theorem applies to the Toeplitz subshifts of
  `rf-toeplitz-subshifts-over-residually-finite-groups` as they are given, and
  `rf-toeplitz-subshifts-act-freely` is not needed for simplicity.
- No infiniteness hypothesis is needed. For finite `X` the hypotheses force a free transitive
  action of a finite group, `R ≅ M_{|X|}(F_2)` and `EL_n(R) = SL_{n|X|}(F_2)`, which is simple.
- Over `F_q` with `q > 2` the argument stops at `g = cI_n` for a locally constant unit `c`, so the
  roots `e_{ij}(e_V u_γ)` are needed there; this claim is over `F_2` only.

Route: `binary-el-simple-iff-minimal-topologically-free-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part1.md`):** PASS. Propositions 3-5 and Theorems 6-7 re-derived. The backward direction is conditional only on the reviewed Steinberg criterion and the transformation-groupoid identification.
