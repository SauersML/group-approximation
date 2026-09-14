---
rg: 2
id: simple-kazhdan-lef-groups-note-open-questions
kind: claim
title: Root of the questions closing the simple Kazhdan LEF note — a finitely presented hyperlinear simple Kazhdan group, and isomorphism rigidity of the subshift groups
root: true
distinct_from:
  simple-kazhdan-lef-groups-note-main-results: that root collects the theorems the note proves; this root collects the two questions it poses at the end.
  hyperlinear-fp-infinite-simple-kazhdan-group: that is the finite-presentation question itself; this is the program root that also carries the rigidity question from the same section of the note.
---

**OPEN (program root, sk swarm, 2026-09-13).** Section "Questions" of
`simple_kazhdan_sofic_group.tex` asks two things, and this claim is their conjunction:

1. Is there a finitely presented infinite simple group with property (T) that is sofic, or at
   least hyperlinear (`hyperlinear-fp-infinite-simple-kazhdan-group`)? No `G_X` is finitely
   presented, since finitely presented LEF groups are residually finite. A positive answer would
   also answer Alekseev--Thom, arXiv:2608.05362, Open problem 6.1.
2. Does `G_X ≅ G_Y` force `X` and `Y` to be strongly orbit equivalent, or even flip conjugate
   (`subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence`, the binary case of
   `subshift-elementary-group-isomorphism-forces-orbit-equivalence`)? Conjugacy or flip
   conjugacy gives an isomorphism.

The route `simple-kazhdan-lef-note-open-questions-conjunction` records the conjunction, so both
questions sit on a live path to a root and show up as frontier holes.

## Attempts
- Finite presentation: `sk-fp-sofic-a`–`d` landed firewalls (gap-sofic approximations are local
  embeddings; isolation of SFT points; no gapped finite unitary models) and no candidate; see the
  Attempts on `hyperlinear-fp-infinite-simple-kazhdan-group`.
- Rigidity: diagonal-preserving isomorphisms force flip conjugacy, matrix-ring isomorphisms force
  strong orbit equivalence, and root-preserving isomorphisms give ring isomorphisms; the missing
  step over `F_2` is standardness, recorded on `subshift-el3-isomorphisms-are-standard-over-f2`.
