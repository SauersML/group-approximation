---
rg: 2
id: fp-simple-group-algebra-amenable-quotient-gives-linear-soficity
kind: claim
title: A finitely presented infinite simple group whose group algebra has an amenable quotient of the Bauer--Blachar--Greenfeld kind is linear sofic
distinct_from:
  rank-modelled-simple-rings-give-linear-sofic-projective-el: that builds rank models of elementary groups from a unital ring rank model; this gets linear soficity of any finitely presented simple group from an amenable quotient of its group algebra, without constructing a model.
  thompson-v-is-f2-linear-sofic: that is the open linear soficity of V over F_2; this is a sufficient condition, which would give it through an ideal of F_2[V].
artifacts:
  - research/artifacts/solve-weakly-sofic-2026-09-13.md
---

**ESTABLISHED (2026-09-13, lane `solve-weakly-sofic`, unreviewed)** by
`fp-simple-amenable-quotient-linear-soficity-proof`.

Let `G` be an infinite finitely presented simple group and `F` a field. Suppose `F[G]` has a nonzero two-sided ideal
`I` such that:
- `I` is finitely generated as a left ideal;
- `F[G]/I` is an amenable algebra;
- `F[G]/I` has no finite-dimensional representations.

Then `G` is `F`-linear sofic.

**Scope.** This is a sufficient condition only. The augmentation ideal fails the third hypothesis. For any other proper
nonzero `I`, `G` embeds in the units of `F[G]/I`, by simplicity. No such ideal is known for `F_2[V]` or `F_2[R^x]`
(`research/artifacts/solve-weakly-sofic-2026-09-13.md`, Section 4).
