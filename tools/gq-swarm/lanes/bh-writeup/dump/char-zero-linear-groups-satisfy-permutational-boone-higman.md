---
rg: 2
id: char-zero-linear-groups-satisfy-permutational-boone-higman
kind: claim
title: Every finitely generated linear group in characteristic zero lies in the permutational Boone--Higman class
distinct_from:
  char-zero-linear-groups-satisfy-boone-higman: that is the plain statement, an embedding in some finitely presented simple group; this puts the same groups in B_A, the class that is closed under direct products, finite-index overgroups and free products.
  fp-self-similar-subgroups-satisfy-permutational-boone-higman: that gives B_A for subgroups of finitely presented self-similar groups and for linear groups over number fields; this is every transcendence degree, through the parameter-coordinate affine hosts.
  polynomial-linear-groups-satisfy-boone-higman: that is the plain property for subgroups of GL_N(Z[1/m][t_1..t_k]); this is membership in B_A for every finitely generated characteristic-zero linear group.
---

**ESTABLISHED (2026-09-13)** through
`char-zero-linear-pbh-via-polynomial-self-similar-hosts`. The route only composes
established nodes, all but the last reviewed by lane `bh-poly-linear-review`.
*Adversarially re-checked end to end (2026-09-18, lane `bh-verify-metabelian`):* no
gap found. Zaremsky's Theorem 1.1 and BFFHZ's Theorem C and Remark 3.5 were re-read at
source, and the parameter-coordinate states were re-derived. See
`research/artifacts/gq-bh-bh-verify-metabelian-report.md`, steps 3–9.

**Statement.** Let `K` be a field of characteristic zero and let `H <= GL_n(K)` be
finitely generated. Then `H` embeds in a group admitting an action of type (A).
So `H` is in `B_A`, as defined in
`boone-higman-type-a-class-closed-under-finite-extensions`. In the language of
Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ), arXiv:2503.21882v2, `H` satisfies
the permutational Boone--Higman conjecture.

**Consequences.**
- **Twisted Brin--Thompson envelope.** By BFFHZ Theorem C, (i) ⟹ (ii), `H` embeds
  in a finitely presented simple twisted Brin--Thompson group.
- **Permanence.** By parts 1--3 of
  `boone-higman-type-a-class-closed-under-finite-extensions`, the following embed
  in finitely presented simple groups:
  - every finite direct product of such groups with each other and with other
    members of `B_A`, such as `Aut(F_n)` or subgroups of finitely presented
    self-similar groups;
  - every finite-index overgroup of such a product.
- **Spherical Artin groups.** Every one of them is in `B_A`
  (`spherical-artin-groups-satisfy-permutational-boone-higman`).

**Credit.**
- **The rational case is known.** Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2,
  l.145--148 of the extracted text: "By now the Boone–Higman conjecture is known
  for many families of groups, e.g., Q-linear groups [Sco84, Zar25a], Aut(Fn)
  [BFFHZ], hyperbolic groups [BBMZ23a], Baumslag–Solitar and free-by-cyclic groups
  [BLIW], and more [BBMZ23b]; in all these cases, the groups not only satisfy (BH)
  but even (PBH)."
- **Where the novelty sits.** The novelty table of
  `research/artifacts/review-bh-polynomial-linear-2026-09-12.md` found no printed
  proof of `char-zero-linear-groups-satisfy-boone-higman`. The upgrade here is one
  more composition, through Zaremsky's envelope and BFFHZ Theorem C. No priority
  is claimed beyond that root's.

**Scope.** Positive characteristic is not covered. The Leavitt tensor hosts of
`positive-char-surface-linear-groups-satisfy-boone-higman` give simple envelopes,
but that node does not ask whether they carry type (A) actions.
