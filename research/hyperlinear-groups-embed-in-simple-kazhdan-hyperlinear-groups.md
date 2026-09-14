---
rg: 2
id: hyperlinear-groups-embed-in-simple-kazhdan-hyperlinear-groups
kind: claim
title: Every finitely generated hyperlinear group embeds in an infinite simple Kazhdan hyperlinear group
distinct_from:
  sofic-groups-embed-in-simple-kazhdan-sofic-groups: that asks for sofic envelopes; this asks for hyperlinear ones, where the envelope needs only tracial unitary models.
  lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple: that proves the envelope theorem for LEF inputs; this asks for the hyperlinear inputs, which include finitely presented non-LEF groups.
---

**OPEN.** Every finitely generated hyperlinear group is a subgroup of an infinite finitely generated simple group
with property (T) that is hyperlinear. Equivalently, since hyperlinearity passes to subgroups, the finitely generated
hyperlinear groups would be exactly the finitely generated subgroups of such groups.

## Attempts

- **Cost of the statement.** It forces an infinite simple Kazhdan hyperlinear group that is not LEF and that contains
  the finitely presented amenable Abels–Prüfer quotient (`simple-kazhdan-envelope-theorems-force-non-lef-hosts`). Every
  known infinite simple Kazhdan group with proved hyperlinearity is LEF: the subshift groups `G_X` and the lamplighter
  hosts.
- **LEF hosts: dead for non-LEF inputs.** Subgroups of LEF groups are LEF. So the envelopes of
  `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` cover exactly the LEF inputs.
- **Boundary groups: undecided.** The nonsofic simple Kazhdan groups over boundary actions of free groups are
  hyperlinear iff `EL_3` over the binary Leavitt algebra is (`boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el`,
  unreviewed). Even a positive answer would not yet contain prescribed hyperlinear inputs.
- **Spatial models: dead.** Compressions of unitary representations without finite-dimensional pieces give no
  Hilbert–Schmidt models of a Kazhdan group (`kazhdan-representations-have-no-hs-compression-models`, unreviewed). Any
  non-LEF envelope needs models that are neither permutational nor spatial.
