---
rg: 2
id: bader-shalom-normal-subgroup-theorem
kind: claim
title: Cocompact lattices with dense projections in products of just-non-compact groups without abelian normal subgroups are just-infinite, with injective projections
distinct_from:
  higher-rank-lattice-normal-subgroups-central-or-finite-index: that is Margulis's theorem for irreducible lattices in higher-rank semisimple Lie groups, whose lattices are linear and hence residually finite; this is the Bader-Shalom theorem for arbitrary compactly generated locally compact factors, the only NST whose hosts can contain infinite simple subgroups.
  burger-mozes-infinitely-transitive-tree-groups: that imports Burger-Mozes local-to-global structure and lattice constructions in products of two trees; this imports the general normal subgroup theorem for uniform lattices in products of abstract locally compact groups.
---

**ESTABLISHED by citation** (`bader-shalom-normal-subgroup-theorem-citation`).

Let `n ≥ 2`. For each `i`, let `G_i` be a non-discrete, compactly generated,
locally compact group that is just-non-compact (not compact, and every proper
Hausdorff quotient compact) and has no nontrivial abelian normal subgroup. Let
`Γ < G_1 × ⋯ × G_n` be a cocompact lattice whose projection to every `G_j` has
dense image. If `n > 3`, assume also that every projection `Γ → ∏_{i≠j} G_i` has
non-discrete image. Then:

1. `Γ` is just-infinite;
2. every projection `p_j : Γ → G_j` is injective;
3. if every `G_i` is hereditarily just-non-compact (every finite-index open
   subgroup is just-non-compact), then `Γ` is hereditarily just-infinite.

**Trust surface.** Statement and proof skeleton are quoted from Caprace's survey
(arXiv:1709.05949, Theorem 4.21). The survey calls this "a slight strengthening of
the original formulation" of Bader–Shalom, Invent. Math. 163 (2006) 415–454,
using [CLB] for `n ≥ 3`. Item 2 is read from the survey's proof, which attributes
it to [CLB, Theorem H]. Neither [BS06] nor [CLB] was re-read. The consumer in this
repository uses only `n = 2`, where the extra non-discreteness hypothesis is
vacuous.
