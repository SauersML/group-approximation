---
rg: 2
id: sofic-amalgam-finite-subgroup-idempotent-traces-are-strict
kind: claim
title: Laminar combinations of finite-subgroup idempotents have positive lifted trace whenever the configuration's intersection amalgam is sofic
distinct_from:
  nested-two-finite-subgroup-idempotents-have-strict-rank: that compares one nested pair from two finite subgroups, whose amalgam is always virtually free; this treats any laminar family of nested and orthogonal idempotents from finitely many finite subgroups and needs soficity of the amalgam of all pairwise intersections, which is not known in general once the intersections form a cycle.
  mixed-finite-subgroup-defects-need-infinite-generation: that excludes a two-subgroup difference when the two subgroups generate a finite group; this excludes every laminar combination, from any number of finite subgroups and at any join, whose intersection amalgam is sofic.
  finite-subgroup-copy-circuits-have-no-recurrent-branching: that constrains exact module isomorphisms among finite-subgroup projectives joined by arbitrary intertwiners; this constrains literal idempotent combinations and says nothing about intertwiners.
artifacts:
  - research/artifacts/finite-subgroup-combination-defects-2026-09-12.md
---

Let `p` be prime, `G` any group, `S = F_p[G]`, and `H_0, ..., H_k <= G` finite subgroups with
`D_ij = H_i n H_j`. Let `A` be the colimit of the inclusions `H_i <- D_ij -> H_j` over all `i < j`.

A **laminar family** is a finite set of distinct idempotents `x_i in M_n(F_p[H_i])` such that for
`i != j`, `x_i x_j = x_j x_i` lies in `{0, x_i, x_j}`. A **laminar combination** is an idempotent
in the span of `1` and the `x_i`.

**Theorem.** If `A` is sofic, every nonzero laminar combination `d` satisfies
`t_p([d S^n]) > 0`, where `t_p` is the lifted trace of
`lifted-trace-detects-finite-subgroup-projectives`. So:
* `[d S^n]` has infinite order in `K_0(S)`;
* for every `m >= 0`, `d (+) 0_m` is not the defect `I - ac` of any pair `ca = I` in
  `M_(n+m)(S)`.

**Forests.** Let `Phi` be the graph on `{0, ..., k}` with an edge `i -- j` whenever `D_ij != 1`.
If `Phi` is a forest, `A` is virtually free, and the theorem holds unconditionally: no hypothesis
on `G` or on the join `<H_0, ..., H_k>`. The case `k = 1` recovers
`nested-two-finite-subgroup-idempotents-have-strict-rank` in characteristic `p`. Differences
`e - f` of nested idempotents from two finite subgroups are therefore never defects, at any join.

**Why the amalgam is the right place.**
* **Transfer.** Every relation of a laminar family is a product of two elements supported in two
  finite subgroups. Such a product is computed on the rectangle `H_i H_j`, where `A -> G` is
  injective. So the multiplication table holds in `F_p[A]`.
* **Rank.** A sofic approximation of `A` gives a faithful rank function which on finite subgroups
  equals the normalized dimension, that is, the lifted trace. It is positive on the nonzero lift
  of `d`, and that value equals `t_p([d S^n])`.

**Consequences for constructions.** A laminar finite-subgroup defect needs:
* at least three finite subgroups whose intersection graph contains a cycle;
* an amalgam `A` that is not sofic.

Sofic joins, amenable joins and forest configurations are all excluded.

**Scope.** Only literal laminar combinations are covered. Idempotents similar to them through
units of unbounded support are not.

ESTABLISHED 2026-09-12 by `sofic-amalgam-finite-subgroup-idempotent-traces-proof` (lane
`w4-kap-join`). Verification requested from `w3-vf-linear`.
