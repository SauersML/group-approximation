---
rg: 2
id: every-fg-rp-group-embeds-in-an-rp-fp-infinity-group
kind: claim
title: "Every finitely generated recursively presented group embeds in a recursively presented group of type FP_infinity"
artifacts:
  - research/artifacts/zp-z1-01-higher-rope-defects-2026-09-13.md
distinct_from:
  every-finitely-presented-group-embeds-in-an-f-infinity-group: that asks for homotopical F_infinity hosts of finitely presented groups; this asks for homological hosts, which may be infinitely presented, of recursively presented groups (the two are equivalent through Fournier-Facio--Zaremsky Theorem A and Higman's theorem)
---

For every finitely generated recursively presented group `Q` there is a
recursively presented group `H` of type `FP_∞` and an injective homomorphism
`Q -> H`. Equivalently, one recursively presented `FP_∞` group contains a
universal finitely presented group.

This is the homological form of the second part of Zaremsky Problem 1.1. It
gives `every-finitely-presented-group-embeds-in-an-f-infinity-group` through
`f-infinity-hosts-via-rp-fp-infinity-hosts` (Theorem A with `n = ∞`), and it
follows from that claim through `rp-fp-infinity-hosts-from-f-infinity-hosts`.
The two routes form a cycle on purpose: they record an equivalence.

## Attempts

- **Higman's rope trick: dead above level 2.** The rope-trick container of
  an infinite `G = F/R` with `R != 1` has infinite-dimensional `H_3(-; Q)`
  (`higman-rope-trick-group-is-never-fp3`). Leary's theorem that every
  countable group embeds in a group of type `FP_2` (arXiv:1610.05813) goes
  through this device (Fournier-Facio--Zaremsky, Remark 3.5), so it stops at
  level 2.
- **One input suffices, with forced features.** Only a universal finitely
  presented group `U` needs a host. Such a host contains Thompson's group `F`
  and every finite group, so it has infinite cohomological dimension and
  torsion of every order.
- **Defect criterion for HNN hosts (standard, to be written as a node).** Let
  `H = HNN(V, L', α, β)` be finitely generated and `M = ∏_Λ ZH`. By the
  Bieri--Eckmann criterion, `H` is of type `FP_n` iff `H_k(H; M) = 0` for
  `1 <= k <= n-1`. By the Mayer--Vietoris sequence of the HNN extension, this
  holds iff `α_* - tβ_*: H_k(L'; M) -> H_k(V; M)` is onto for
  `1 <= k <= n-1` and one-to-one for `0 <= k <= n-2`. A rope needs the
  homological defects of the edge group and the vertex group to cancel in
  every degree up to `n-1`. Leary's rope achieves this only in degree 1.
- **Preliminary (unreviewed): vertex groups `P x G` with `α = ι x 1` through a
  group `P` of type `FP_∞` look blocked.** On `M` the map `α_*` factors through
  `H_k(P; M) = 0` in positive degrees. If `ker(L' -> G)` is also of type
  `FP_∞`, then `β_*` compares `G`-homology of the coinvariant modules `M_N`
  and `M_P`, and the collapse `M_N -> M_P` is not injective. Work in the lane
  artifact.
