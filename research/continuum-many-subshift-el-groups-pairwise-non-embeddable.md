---
rg: 2
id: continuum-many-subshift-el-groups-pairwise-non-embeddable
kind: claim
title: There are continuum many infinite finitely generated simple Kazhdan LEF groups G_X, none isomorphic to a subgroup of another
distinct_from:
  subshift-elementary-group-word-problem-degree: that computes WP(G_X) ≡_T L(X) and concludes uncountably many isomorphism classes; this upgrades nonisomorphic to pairwise non-embeddable, using an antichain of Turing degrees and the reduction of word problems to overgroups
  positive-entropy-el-groups-avoid-low-complexity-hosts: that obstructs embeddings through LEF growth and complexity; this obstructs them through computability, for families of equal complexity
artifacts:
  - research/artifacts/sk-free-7-non-embeddability-2026-09-13.md
---

**ESTABLISHED (unreviewed).** There is a family {X_i : i ∈ I}, |I| = 2^{ℵ_0}, of Sturmian subshifts such that:
- every G_{X_i} = EL_3(LC(X_i,F_2) ⋊ Z) is an infinite, finitely generated, simple, Kazhdan, LEF group;
- for i ≠ j, G_{X_i} is not isomorphic to any subgroup of G_{X_j}.

**Mechanism.** A finitely generated subgroup has word problem reducible to that of the overgroup. The word problem of G_{X_α} has the degree of α, and the Turing degrees contain an antichain of size continuum.

**For the note** (landed rev3, l.368–369): "Every Turing degree occurs, so there are continuum many pairwise nonisomorphic groups $G_X$" can become "…so there are continuum many groups $G_X$, none of which is isomorphic to a subgroup of another". See `research/artifacts/sk-free-7-proposal-2026-09-13.md`.

Route: `continuum-many-subshift-el-groups-pairwise-non-embeddable-proof`.

**Review (sk-verify-15, 2026-09-13): PASS.** Steps 1–4 re-derived: word problems reduce many-one along embeddings of f.g. groups; α_x = 0.(x⊕c) has α_x ≡_T x and is irrational; WP(G_{X_α}) ≡_T α; an embedding would give x ≤_T y. Optional wiring W1: add `topologically-free-matricial-crossed-el-simple-kazhdan-lef` (PASS twice) to `requires`, since `finite-model-subshift-elementary-groups-simple-kazhdan-lef` carries no review line. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §1.
