---
rg: 2
id: spherical-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: Every spherical-type Artin group lies in the permutational Boone--Higman class
distinct_from:
  spherical-artin-groups-satisfy-boone-higman: that is the plain statement, an embedding in some finitely presented simple group; this is membership in B_A, which is closed under direct products and finite-index overgroups.
  e-type-artin-groups-satisfy-permutational-boone-higman: that is the permutational property for E_6, E_7 and E_8 only, the hypothesis of the Crisp reduction; this is every spherical type, including F_4, H_3 and H_4.
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that is the conditional reduction of this statement to the E types through Crisp's embedding; this is the unconditional statement, reached through linearity instead.
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ's Aut(F_n) theorem, which reaches types A, B, D and I_2(m); this is every spherical type, through linearity over Q(x,y).
  char-zero-linear-groups-satisfy-permutational-boone-higman: that is membership in B_A for every finitely generated characteristic-zero linear group; this is the named class of spherical Artin groups, which that theorem reaches through their linearity over Q(x,y).
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**ESTABLISHED (2026-09-13)** through
`spherical-artin-pbh-via-char-zero-linear-groups`. Not independently reviewed.

**Statement.** Every Artin group of spherical type embeds in a group admitting an
action of type (A), so it lies in `B_A`
(`boone-higman-type-a-class-closed-under-finite-extensions`). In the language of
Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ), arXiv:2503.21882v2, it satisfies the
permutational Boone--Higman conjecture. By their Theorem C, (i) ⟹ (ii), it embeds
in a finitely presented simple twisted Brin--Thompson group.

**New types.**
- **Already in the graph:** A_n, B_n = C_n, D_n and I_2(m), through BFFHZ's
  Aut(F_n) theorem (`aut-free-groups-satisfy-permutational-boone-higman`).
- **New here:** E_6, E_7, E_8, F_4, H_3 and H_4.
- **Who lists them as open.** BFFHZ, l.67--68 of the extracted text
  (`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`, read 2026-09-13): "For
  spherical and Euclidean Artin groups, the Boone–Higman conjecture remains open
  for the exceptional type spherical Artin groups". The plain form is already
  settled in `spherical-artin-groups-satisfy-boone-higman`. This node adds the
  permutational form.

**Consequences.** By parts 1--3 of
`boone-higman-type-a-class-closed-under-finite-extensions`, the following embed in
finitely presented simple groups:
- every finite direct product of spherical Artin groups, with each other and with
  other members of `B_A`;
- every finite-index overgroup of such a product;
- every group commensurable with a spherical Artin group.

The hypothesis of `spherical-artin-boone-higman-reduces-to-e6-e7-e8` now holds, so
that reduction stays as a second proof of the same statement.

**Credit.** This follows at once from
`char-zero-linear-groups-satisfy-permutational-boone-higman` and the linearity
import. Whatever novelty there is sits with
`char-zero-linear-groups-satisfy-boone-higman`, and no priority is claimed beyond
that root's.

**Verification (bh-verify-artin, 2026-09-18; lane check, not an external review).** PASS conditional. This one-line composition checks and is carried entirely by `char-zero-linear-groups-satisfy-permutational-boone-higman`. Two status lines disagree: that node's line says it is not independently reviewed, while `research/artifacts/review-pbh-charzero-spherical-2026-09-13.md` gives it PASS. Both reviews are internal. See `research/artifacts/gq-bh-bh-verify-artin-report.md`.
