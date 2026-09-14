---
rg: 2
id: sofic-non-lef-infinite-simple-kazhdan-group-exists
kind: claim
title: Some infinite simple Kazhdan group is sofic and not LEF
distinct_from:
  simple-kazhdan-linear-sofic-non-lef-group-exists: that certifies linear soficity over a finite field for a non-LEF simple Kazhdan group; this asks for soficity in the normalized Hamming metric.
  sofic-universal-envelope-forces-non-lef-simple-kazhdan: that is the implication from a universal sofic host theorem to a group like this; this is the existence question itself.
  hyperlinear-fp-infinite-simple-kazhdan-group: that asks for a finitely presented example; a sofic answer there is one way to settle this claim.
---

**OPEN.** Some infinite simple group with property (T) is sofic and not locally embeddable into
finite groups. Kazhdan groups are finitely generated, so LEF makes sense for them. The negation is
the question "Is every sofic infinite simple Kazhdan group LEF?", which the sk-questions-section
proposal adds to the Questions section of `simple_kazhdan_sofic_group.tex`
(`research/artifacts/sk-questions-section-proposal-2026-09-13.md`).

**Why it is the pivot of the note's questions.**
- Finite presentation. A finitely presented infinite simple sofic Kazhdan group is not LEF: a
  finitely presented LEF group is residually finite (`finitely-presented-lef-groups-are-residually-finite`),
  and an infinite simple group is not. So a sofic answer to `hyperlinear-fp-infinite-simple-kazhdan-group`
  proves this claim, and a proof that every sofic infinite simple Kazhdan group is LEF answers the sofic
  form of that question negatively.
- Hosts. A universal sofic host (`sofic-groups-embed-in-simple-kazhdan-sofic-groups`) proves this claim
  (`sofic-universal-envelope-forces-non-lef-simple-kazhdan`).
- Model test.
  - Finite simple groups are Kazhdan, sofic and LEF; "infinite" excludes them.
  - The groups `G_X` and the lamplighter hosts of `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple`
    are sofic because they are LEF, so they are not examples.
  - The groups `S_N` of `simple-kazhdan-linear-sofic-non-lef-group-exists` are not LEF and are linear sofic
    over a finite field. Their soficity is unknown, so they are the nearest candidates.

## Attempts
- **Linear targets.** Dead as a source of examples. By `gap-sofic-approximations-are-local-embeddings`, a
  sofic approximation of `EL_n(R)` through `GL_N(F_q)` acting on vectors, affine spaces or lines is
  automatically a local embedding, so it only ever witnesses LEF.
- **Upgrading rank models.** The non-LEF host `S_N` has rank-metric models. On vectors a rank defect `r`
  becomes a Hamming defect `1 - q^(-O(r))` (the barrier recorded on
  `sofic-groups-embed-in-simple-kazhdan-sofic-groups`), so these models do not give soficity.
- **Finite presentation.** The Kac–Moody and Titz Mite–Witzel candidates on
  `hyperlinear-fp-infinite-simple-kazhdan-group` have unknown soficity (`km-246-lattice-is-sofic`, OPEN).
- **Bounded literature check (sk-questions-section, 2026-09-13).** No sofic Kazhdan group that is not LEF,
  simple or not, was located.
  - The sk-questions-ggt sweep: 25 sources, including grep of the Kourovka Notebook for "sofic" and "LEF".
  - Alekseev–Thom, arXiv:2608.05362, §5–6. Among sofic non-residually-finite Kazhdan groups they name only
    Thom's group, which is LEF (sk-novelty-prior-art part 1). Their Open problem 6.1 asks for finitely
    presented examples.
  - One web search: "sofic group with property (T) that is not LEF".

  This is not a complete search.
