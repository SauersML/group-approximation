---
rg: 2
id: co-amenable-subgroups-transfer-hyperfinite-orbit-relations
kind: claim
title: A co-amenable subgroup with hyperfinite measured orbit relation forces the whole group's orbit relation to be hyperfinite
distinct_from:
  thompson-f-interval-orbit-relation-is-hyperfinite: that proves hyperfiniteness of one orbit relation of F; this is a general transfer from a co-amenable subgroup to the ambient group, which needs no amenability of the subgroup.
  thompson-f-interval-orbit-relation-is-nonamenable: that is the refuted hope that F's own interval relation is non-amenable; this passes an amenable orbit relation from a co-amenable subgroup up to any overgroup acting on the same space.
  rokhlin-maximality-ascends-co-amenable-subgroups: that transfers a Rokhlin-entropy statement along co-amenable subgroups; this transfers hyperfiniteness of orbit relations.
---

**ESTABLISHED.** Let `G` be a countable group acting by Borel automorphisms on a standard Borel
space `X`, and let `μ` be a `σ`-finite Borel measure on `X` whose null sets are `G`-invariant.
Let `H ≤ G` be co-amenable (there is a `G`-invariant mean on `G/H`). If the orbit relation
`R_H` is `μ`-hyperfinite, then the orbit relation `R_G` is `μ`-hyperfinite.

The subgroup `H` need not be amenable, and its point stabilizers may be non-amenable.

**Contrapositive, as used.** If `R_G` is not `μ`-hyperfinite, then no subgroup `H` with
`μ`-hyperfinite `R_H` is co-amenable in `G`. Monod's non-amenability mechanism for piecewise
projective groups (non-amenable Lebesgue orbit relation) therefore obstructs co-amenability in
`G` of every subgroup whose own orbit relation is amenable, whether or not that subgroup is
amenable.

**Scope and trust surface.** The proof is elementary except for the Connes–Feldman–Weiss
theorem ("`μ`-amenable iff `μ`-hyperfinite"), which is imported verbatim through Elek–Timár,
arXiv:2408.12565. The analogue for Zimmer-amenable *actions* is used as known by Monod
(arXiv:1209.5229, `vn_pnas3.tex` l.322: "If the $\Gamma$-action on $\PP^1$ were amenable, so
would be the $L$-action (by co-amenability of the lattice)."). That version is useless for
Thompson's `F`: amenability of an action forces amenable stabilizers, and stabilizers of the
natural `F`-action contain `F`. The relation version proved here needs no stabilizer
hypothesis.

Proof route: `co-amenable-hyperfinite-transfer-proof`.
