---
rg: 2
id: fg-infinite-simple-groups-are-minimally-almost-periodic
kind: claim
title: Every finitely generated infinite simple group is minimally almost periodic
distinct_from:
  binary-leavitt-unit-group-is-minimally-almost-periodic: that proves minimal almost periodicity for one group through its embedded Thompson subgroup and characteristic-two normal generation; this proves it for every finitely generated infinite simple group through Peter–Weyl and Malcev's theorem.
  fournier-facio-group-is-minimally-almost-periodic: that concerns the Fournier–Facio group, which is not simple, by an argument specific to it; this covers exactly the finitely generated infinite simple groups.
artifacts:
  - research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md
---

ESTABLISHED. Let `G` be a finitely generated infinite simple group. Then every homomorphism from `G`
to a compact group is trivial. In particular `G` has no nontrivial finite quotient and no nontrivial
finite-dimensional unitary representation.

Proof: Section 2 of the artifact. A nontrivial homomorphism is detected by a finite-dimensional
unitary representation (Peter–Weyl). The image is then a finitely generated linear group, hence
residually finite (Malcev). By simplicity the representation is injective, so `G` would be an
infinite residually finite simple group, which cannot exist.

Hosts covered:
* `R^x` (`binary-leavitt-unit-group-is-simple`);
* the scalar quotients of `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`;
* every host of `countable-group-embeds-in-fg-simple-kazhdan-group`.
