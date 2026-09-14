---
rg: 2
id: simple-kazhdan-lef-groups-note-open-questions
kind: claim
title: Root of the questions closing the simple Kazhdan LEF note — finite presentation, sofic hosts, sofic versus LEF, and isomorphism rigidity of the subshift groups
root: true
distinct_from:
  simple-kazhdan-lef-groups-note-main-results: that root collects the theorems the note proves; this root collects the questions it poses at the end.
  hyperlinear-fp-infinite-simple-kazhdan-group: that is the finite-presentation question itself; this is the program root that also carries the other questions from the same section of the note.
---

**OPEN (program root, sk swarm, 2026-09-13).** Section "Questions" of
`simple_kazhdan_sofic_group.tex` asks the following, and this claim is their conjunction:

1. Is there a finitely presented infinite simple group with property (T) that is sofic, or at
   least hyperlinear (`hyperlinear-fp-infinite-simple-kazhdan-group`)? No `G_X` is finitely
   presented, since finitely presented LEF groups are residually finite. A sofic answer would
   also answer Alekseev--Thom, arXiv:2608.05362, Open problem 6.1.
2. Does `G_X ≅ G_Y` force `X` and `Y` to be strongly orbit equivalent, or even flip conjugate
   (`subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence`, the binary case of
   `subshift-elementary-group-isomorphism-forces-orbit-equivalence`)? Conjugacy or flip
   conjugacy gives an isomorphism.
3. Is every finitely generated sofic group a subgroup of an infinite finitely generated simple
   Kazhdan sofic group (`sofic-groups-embed-in-simple-kazhdan-sofic-groups`)? This is the sofic
   analogue of the note's LEF characterization. The revision 4 draft (sk-editor-4) poses it.
4. Is every sofic infinite simple Kazhdan group LEF? The claim recorded is the negative answer
   (`sofic-non-lef-infinite-simple-kazhdan-group-exists`), which a sofic answer to question 1 or a
   positive answer to question 3 would give. Proposed in
   `research/artifacts/sk-questions-section-proposal-2026-09-13.md`.

The route `simple-kazhdan-lef-note-open-questions-conjunction` records the conjunction, so every
question sits on a live path to a root and shows up as a frontier hole.

## Attempts
- Finite presentation: `sk-fp-sofic-a`–`d` landed firewalls (gap-sofic approximations are local
  embeddings; isolation of SFT points; no gapped finite unitary models) and no candidate; see the
  Attempts on `hyperlinear-fp-infinite-simple-kazhdan-group`.
- Rigidity: diagonal-preserving isomorphisms force flip conjugacy, matrix-ring isomorphisms force
  strong orbit equivalence, and root-preserving isomorphisms give ring isomorphisms; the missing
  step over `F_2` is standardness, recorded on `subshift-el3-isomorphisms-are-standard-over-f2`.
- Sofic hosts: rank-metric (linear sofic) hosts exist for every finitely generated sofic group
  (`sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups`, unreviewed). The rank-to-Hamming gap
  is the whole remaining content; see the Attempts on `sofic-groups-embed-in-simple-kazhdan-sofic-groups`.
- Sofic versus LEF: linear targets over finite fields only produce local embeddings, and the known
  non-LEF simple Kazhdan groups are only linear sofic; see the Attempts on
  `sofic-non-lef-infinite-simple-kazhdan-group-exists`.
