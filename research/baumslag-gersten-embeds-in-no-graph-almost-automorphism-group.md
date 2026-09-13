---
rg: 2
id: baumslag-gersten-embeds-in-no-graph-almost-automorphism-group
kind: claim
title: Every homomorphism from the Baumslag--Gersten group to the almost-automorphism group of the path space of a finite graph kills a, so BG embeds in no topological full group of a one-sided shift of finite type
distinct_from:
  baumslag-gersten-embeds-in-no-rover-nekrashevych-group: that excludes almost-automorphism groups of one regular rooted forest, a single cone type; this excludes the almost-automorphism group of the path space of any finite graph, which covers one-sided shifts of finite type with several cone types.
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**Statement.** Let `BG = < a, t | b a b^-1 = a^2 >` with `b = t a t^-1`. Let `E`
be a finite directed graph with no sinks, and let `A(E)` be as in
`graph-path-almost-automorphism-proper-power-is-equicontinuous`.
- Every homomorphism `φ : BG → A(E)` has `φ(a) = 1`, so it factors through
  `BG/<<a>> = Z`.
- Hence `BG` embeds in no subgroup of any `A(E)`:
  - no topological full group of a one-sided shift of finite type;
  - no group of graph-path homeomorphisms that act piecewise by prefix
    replacement followed by path isometries;
  - no finitely presented simple group inside such a group.

**Not covered.**
- Brin--Thompson groups `nV`.
- Twisted Brin--Thompson groups `SV_G`.
- Rational similarity groups with non-isometric sections.
- Full groups of non-expansive groupoids.

The proof is `baumslag-gersten-graph-host-obstruction-proof`.
