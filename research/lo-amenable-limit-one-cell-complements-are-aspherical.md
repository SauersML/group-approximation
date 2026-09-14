---
rg: 2
id: lo-amenable-limit-one-cell-complements-are-aspherical
kind: claim
title: A one-cell complement whose group is a limit of left-orderable amenable groups has vanishing first L²-Betti number and is aspherical
distinct_from:
  osin-thom-lo-amenable-limits-satisfy-b1-bound: that is Osin--Thom's inequality for every finitely generated limit of left-orderable amenable groups; this specializes it to one-cell complements, where the first Betti number is one, and adds asphericity.
  one-cell-complement-groups-have-vanishing-first-l2-betti: that is the open vanishing statement for every one-cell complement; this proves it under the limit hypothesis.
  ascending-hnn-one-cell-complements-have-vanishing-l2-b1: that proves vanishing when the group is an ascending HNN extension of a finitely generated group; this uses a marked-group limit hypothesis instead, and this lane did not compare the two classes.
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

**ESTABLISHED** through `lo-amenable-limit-one-cell-asphericity-proof`.

Let `L` be a finite connected contractible 2-complex, `e` an open 2-cell, `K = L − e` and
`G = π₁(K)`. If `G` is a limit of left-orderable amenable groups in the space of marked group
presentations, then `b₁^(2)(G) = 0` and `K` is aspherical.

## Scope

- **Residual form.** The hypothesis holds when `G` is residually (left-orderable and amenable). That
  class is closed under subgroups and finite direct products. So for each `n` the image of `G` in a
  finite product of such quotients, chosen so that no nontrivial element of word length at most `n`
  dies, lies in the class, and these marked quotients converge to `G`.
- **What it does not reach.** A one-cell complement group other than `Z` is never residually
  nilpotent. `G^ab ≅ Z`, and `Λ²Z = 0`, so `γ₂G = γ₃G`, hence `γ_nG = G'` for every `n ≥ 2`.
  Residual nilpotence would then force `G' = 1` and `G = Z`. The residually torsion-free nilpotent
  examples that Osin--Thom highlight never apply here.
- Osin--Thom state that their theorem has no nontrivial application to the Whitehead problem
  (`osin-thom-lo-amenable-limit-citation`, l.472). This lane found no one-cell complement that is
  covered here and not by `ascending-hnn-one-cell-complements-have-vanishing-l2-b1`, and did not
  search for one.
