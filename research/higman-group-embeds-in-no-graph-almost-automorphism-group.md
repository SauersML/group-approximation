---
rg: 2
id: higman-group-embeds-in-no-graph-almost-automorphism-group
kind: claim
title: Higman's four-generator group has only the trivial homomorphism to the almost-automorphism group of the path space of any finite graph
distinct_from:
  higman-group-embeds-in-no-almost-automorphism-group: that excludes almost-automorphism groups of one regular rooted forest; this excludes the almost-automorphism group of the path space of any finite graph, which covers one-sided shifts of finite type with several cone types.
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**Statement.** Let
`H4 = < g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i ∈ Z/4 >`. Let `E`
be a finite directed graph with no sinks, and let `A(E)` be as in
`graph-path-almost-automorphism-proper-power-is-equicontinuous`.
- Every homomorphism `H4 → A(E)` is trivial.
- So `H4` embeds in no subgroup of any `A(E)`, in particular in no topological
  full group of a one-sided shift of finite type.

**Not covered.**
- Brin--Thompson groups `nV`.
- Rational similarity groups with non-isometric sections.
- Full groups of non-expansive groupoids.

The proof is `higman-group-graph-host-obstruction-proof`.
