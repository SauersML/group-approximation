---
rg: 2
id: finite-subgroup-idempotent-ideals-admit-no-proper-group-shift
kind: claim
title: A group element never properly shifts the right ideal of a finite-subgroup idempotent, and in general a proper shift needs a non-directly-finite HNN extension
distinct_from:
  nested-two-finite-subgroup-idempotents-have-strict-rank: that compares two-sided nested idempotents by rank; this treats the one-sided containment g e A ⊆ e A, where the ranks agree and give no contradiction, and transfers the containment to an HNN extension
  two-piece-s0-lifts-telescope-to-a-corner: that computes when a two-piece lift pair has a unit product; this is a general group-ring theorem about translated idempotent right ideals, used to kill the triangular case on finite supports
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

**ESTABLISHED** by route `finite-subgroup-idempotent-ideal-shift-proof`. Re-derivation requested from
`w4-vf-linear-b`.

Let `G` be a group, `k` a field, `K <= G` a subgroup, `g` in `G`, `D = K ∩ gKg^(-1)`, and let `H` be the HNN extension
of `K` along conjugation by `g` from `g^(-1)Dg` to `D`. Let `e` in `M_n(k[K])` be an idempotent.

**Theorem A.** If `[g] e M_n(k[G]) ⊆ e M_n(k[G])`, equivalently `(I - e)[g]e = 0`, and `M_n(k[H])` is directly
finite, then `[g] e M_n(k[G]) = e M_n(k[G])`.

**Corollary B (unconditional).** If `K` is finite, then `H` is virtually free and `M_n(k[H])` is directly finite. So
for every group `G`, field `k`, finite subgroup `F`, idempotent `e` in `M_n(k[F])` and group element `g`, a containment
`[g] e M_n(k[G]) ⊆ e M_n(k[G])` is an equality.

Proof idea:
- the equation `(I - e)[g]e = 0` lives on the single double coset `KgK`, whose group algebra is
  `k[K] ⊗_(k[D]) k[K]` in `G` and in `H` alike, so the equation holds in `H`;
- in `H`, `x = [t]e + (I - e)` is left invertible, so it is invertible and `eB = [t]e[t^(-1)]B`;
- push the equality back to `G`.

Artifact Sections 0–2.

Scope: the shift must be a group element. For a unit `w` of `k[G]` in place of `[g]`, the product `(I - e)we` is spread
over many double cosets, and the argument gives nothing.
