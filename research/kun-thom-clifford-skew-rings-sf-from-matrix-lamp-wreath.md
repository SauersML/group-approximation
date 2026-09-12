---
rg: 2
id: kun-thom-clifford-skew-rings-sf-from-matrix-lamp-wreath
kind: route
title: Embed every Kun--Thom Clifford skew ring locally in a matrix-lamp wreath and use its stable finiteness
target: kun-thom-clifford-skew-rings-are-stably-finite
requires:
  - matrix-lamp-wreath-algebras-are-stably-finite
  - oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

**DEAD.** Invalidated by `infinite-clique-clifford-algebras-have-no-bounded-spin-models`.

The plan was to extend the spin embedding of Proposition 1.1 from orientable graphs to every invariant graph,
mapping each generator to a bounded-support element of some matrix-lamp wreath `B_(X')` over the same
group. Stable finiteness of `B_(X')` would then pass to every `A_S`.

The step fails for the complete graph. Over finite fields, pairwise anticommuting involutions with bounded
supports in an infinite tensor product of matrix algebras form only finite families. The oriented graphs
are still covered by `oriented-clifford-skew-rings-sf-from-matrix-lamp-wreath`.
