---
rg: 2
id: whitehead-one-cell-counterexamples-have-positive-first-l2-betti
kind: claim
title: A non-aspherical one-cell complement of a finite contractible 2-complex has positive first L²-Betti number and no amenable normalish subgroup
distinct_from:
  finite-2-complex-with-zero-second-l2-betti-is-aspherical: that is the L² asphericity criterion for arbitrary finite 2-complexes; this specializes it to Whitehead's finite one-cell case, where χ = 0, and adds the group-theoretic consequences.
  nonaspherical-subcomplex-of-contractible-2-complex-exists: that asserts a Whitehead counterexample exists; this constrains the fundamental group of any finite one-cell counterexample.
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

**ESTABLISHED** through `whitehead-one-cell-positive-l2-betti-proof`.

Let L be a finite connected contractible 2-complex, e an open 2-cell of L, K = L − e,
and G = π₁(K). If K is not aspherical, then:
1. b₁^(2)(G) > 0;
2. G contains no amenable normalish subgroup. In particular, G is not amenable and has
   no infinite amenable normal subgroup.

Equivalently, b₁^(2)(G) = 0 makes K aspherical.

No novelty is claimed. The deficiency-one criterion behind it is likely in Hillman,
*Four-manifolds, geometries and knots*, Chapter 2 (not checked).
