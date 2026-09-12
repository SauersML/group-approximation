---
rg: 2
id: finitary-split-extension-surjunctivity-permanence
kind: claim
title: A split extension with a finitary site structure over a surjunctive group is surjunctive
distinct_from:
  rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive: that is the permutational wreath instance with its own direct proof; this isolates the axioms the proof uses and also covers free kernels with cocycle actions, such as group doubles.
  surjunctive-guard-subgroups-force-surjectivity: that concerns automata preserving unions of cosets of one surjunctive guard subgroup inside an arbitrary group; this concerns all automata over a class of groups.
artifacts:
  - research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

Let `W = N semidirect_alpha G` and let `X` be a left `G`-set. Suppose that:

* **(D)** for each finite `S` in `X` there is an epimorphism `p_S: N -> N_S`
  onto a residually finite group, with `N_empty = 1`;
* **(D')** for `U` contained in `S` there are compatible embeddings
  `iota_(U,S): N_U -> N_S`,

and that the following hold:

* **(A1) Detection.** Finitely many nontrivial elements of `N` are all
  detected by one `p_S`.
* **(A2) Finite support.** Each `n` has a finite `L(n)` in `X` such that
  `p_S(alpha_g n) = iota_(U,S) p_U(alpha_g n)` whenever `gL(n)` misses `S\U`.
* **(A3) Stabilizer invariance.** `p_S o alpha_k = p_S` for `k` fixing `S`
  pointwise.

Then `W` is surjunctive if and only if `G` is surjunctive.

**Instances.**
1. Permutational wreath products with residually finite lamps
   (`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`).
2. Group doubles `G *_Gamma G ~= F(X \ {x_0}) semidirect G` with
   `alpha_g(e_x) = e_(gx) e_(gx_0)^-1` (`doubles-of-surjunctive-groups-are-surjunctive`).

**Proof outline.**
1. Transplant an injective automaton to the coset spaces
   `ker(q o p_S)\W ~= Q x G` for finite quotients `q: N_S -> Q`. They
   separate `W` by (A1).
2. By (A2), the rule is uniform off strata that are right cosets of point
   stabilizers, and slices over left cosets of `Q_U` carry the `U`-level
   transplants.
3. By (A3), the transplants commute with left translation by the stabilizer
   intersections `G_U`.
4. Peel in order of cardinality. The coset-region lemma applied to the
   surjunctive subgroups `G_U` finishes the proof.

Full proof in the linked artifacts.

This does not treat groups without such a split finitary structure, including
the binary Leavitt unit group, Thompson's `V`, general amalgams `A *_C B` with
`A != B`, and non-split extensions.
