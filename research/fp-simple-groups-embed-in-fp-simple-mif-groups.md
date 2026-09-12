---
rg: 2
id: fp-simple-groups-embed-in-fp-simple-mif-groups
kind: claim
title: Every finitely presented simple group embeds in a finitely presented simple mixed-identity-free group
distinct_from:
  boone-higman-conjecture: that embeds decidable finitely generated groups in finitely presented simple groups; this starts from a finitely presented simple group and asks for a finitely presented simple overgroup with no mixed identities, which is what makes it land in a twisted Brin--Thompson group.
  aut-free-groups-satisfy-permutational-boone-higman: that imports the Aut(F_n) theorem and the universality of twisted Brin--Thompson groups among finitely presented simple MIF groups (Corollary D); this is the open question of whether every finitely presented simple group has such an overgroup.
---

**OPEN.** Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, pose it as
Question 3.4: "Does every finitely presented simple group embed in a finitely
presented simple MIF group?" The question number was confirmed by lane
`bh-reviewer` from the PDF text on MSI (review artifact §12, 43f7e25d3).

**Why it matters.**
- **Universality:** their Corollary D says finitely presented simple twisted
  Brin--Thompson groups are universal among finitely presented simple highly
  transitive groups, and more generally among finitely presented simple MIF
  groups.
- **BFFHZ's remark:** a positive answer makes the permutational Boone--Higman
  conjecture equivalent to Boone--Higman, and a negative answer refutes the
  permutational conjecture. The route for the first half is
  `permutational-boone-higman-via-mif-envelopes`.
- **Not verified here:** that remark was not re-derived line by line.

## Attempts

None recorded in Cairn. The claim was opened on 2026-09-12 by lane
`bh-twisted-brin-thompson` as the explicit hinge between the two conjectures.
The natural first test is the repo's finitely presented simple groups not built
as twisted Brin--Thompson groups, in particular the Leavitt unit groups
`L_(F_2)(1,2)^x` and `(L⊗L)^x`. Do they satisfy a mixed identity, or embed in an
MIF finitely presented simple group? That was not attempted.
