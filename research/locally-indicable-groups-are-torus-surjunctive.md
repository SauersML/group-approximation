---
rg: 2
id: locally-indicable-groups-are-torus-surjunctive
kind: claim
title: An injective torus automaton whose degree support generates a locally indicable group has invertible degree matrix and is onto, so locally indicable groups such as BS(2,3) are torus-surjunctive at every dimension
distinct_from:
  torus-degree-regular-on-prime-power-residual-support: that needs the support subgroup to be residually prime-power; this needs it locally indicable, which covers groups that are not residually finite, such as BS(2,3), and corrects that node's reading that augmentation-only arguments work exactly on RPP support.
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that needs the ambient group residually finite, or d = 1 with Q[G] a domain; this works at every d over non-residually-finite locally indicable groups.
  injective-torus-automata-have-regular-degree: that is C2 for every group (OPEN); this proves C2 on locally indicable support subgroups only.
  every-group-is-torus-surjunctive: that is torus surjunctivity for every group (OPEN); this is the locally indicable case.
artifacts:
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
  - experiments/torus-fox-witness-2026-09-17/check_fox_witness.py
---

Let `tau` be an injective continuous `G`-equivariant self-map of `(T^d)^G`, with degree matrix
`D = D(tau) in M_d(Z[G])` and support subgroup `H = <supp D>`.

**Claim.**
- (a) If `H` is locally indicable, then `xi -> xi D` is injective on `Q[G]^d`, and `tau` is onto.
- (b) In that case `tau` is also a homeomorphism, and `D(tau) in GL_d(Z[G])` with inverse
  `D(tau^{-1})`.
- (c) So every locally indicable group is torus-surjunctive at every `d`.

New host: `BS(2,3) = <x, y | y^{-1} x^2 y = x^3>`. It is torsion-free one-relator, hence
locally indicable. It is not residually finite, hence not RPP, and being finitely presented it
is not LEF. So no earlier node covers it at `d >= 2`.

Thompson's group `F` is bi-orderable, hence locally indicable (recalled), so it is covered too.

This answers both first tests named in need 7c18e718: `d = 2` over `BS(2,3)` and over Thompson's
`F`. Both answers are positive, and neither needs any approximation of the group.

With `torus-degree-regular-on-prime-power-residual-support`, a counterexample to C2 must have a
support group that is neither RPP nor locally indicable.

**ESTABLISHED 2026-09-18** by [[locally-indicable-groups-are-torus-surjunctive-proof]].
