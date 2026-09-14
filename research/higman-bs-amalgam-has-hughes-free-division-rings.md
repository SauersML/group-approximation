---
rg: 2
id: higman-bs-amalgam-has-hughes-free-division-rings
kind: claim
title: The Baumslag--Solitar amalgams inside Higman's group have Hughes-free division rings over every division ring
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports Hughes-free existence for amenable, residually torsion-free nilpotent and free-by-cyclic groups, and the source gets these vertex groups only in characteristic zero through Strong Atiyah; this proves existence for BS(1,2) *_Z BS(1,2) in every characteristic through a split extension by BS(1,2) with locally free kernel.
  higman-group-splits-as-amalgams-over-free-subgroups: that gives the splittings and soficity of the vertex groups; this gives their Hughes-free division rings.
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

**ESTABLISHED** by [[higman-bs-amalgam-has-hughes-free-division-rings-proof]].

Let `G_1 = <a,b,c | b^a = b^2, c^b = c^2>` with `x^y = y^(-1) x y`. Then:

1. `G_1 = K ⋊ <a,b>`, where `<a,b> ≅ BS(1,2)` and `K`, the kernel of the retraction `c -> 1`, is locally free;
2. `G_1` is locally indicable;
3. for every division ring `k`, the group ring `k[G_1]` has a Hughes-free division ring `D_(k G_1)`.

By relabelling, the same holds for `G_2 = <c,d,a>`, `G_3 = <b,c,d>` and `G_4 = <d,a,b>` of
[[higman-group-splits-as-amalgams-over-free-subgroups]].
