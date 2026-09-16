---
rg: 2
id: length16-residue-classes-virtually-free-by-cyclic
kind: claim
title: 172 of the 211 length-16 unpeelable residue classes, including 139 of the 141 with no landed Linton certificate, are virtually free-by-cyclic, residually finite and sofic
distinct_from:
  length15-16-free-piece-residue-classes-hyperbolic-special: that proves hyperbolicity and virtual specialness for 70 length-16 classes with a visibly free Magnus piece; this proves virtual free-by-cyclicity and soficity for 172 classes, 107 of which that node does not cover, by a different certificate.
  unpeelable-extreme-one-relator-groups-sofic: that is the open soficity claim for all unpeelable relators; this settles an explicit finite list of length-16 relators.
artifacts:
  - research/artifacts/or-length16-nonfree-residue-2026-09-16.md
  - research/artifacts/one-relator-linton-graph-certificates-scripts/census3_16.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_words16.out
  - research/artifacts/or-length15-residue-scripts/vfib.py
  - research/artifacts/or-length15-residue-scripts/verify.py
  - experiments/or-length16-nonfree-residue-2026-09-16/recheck.py
  - experiments/or-length16-nonfree-residue-2026-09-16/accounting.py
  - experiments/or-length16-nonfree-residue-2026-09-16/accounting.out
---

Proved through `length16-residue-virtual-fibring-certificates`. The certificates are
computer-checked by three separately written checkers: `verify.py` (length-15 lane), `recheck.py`
(this lane) and `referee_check.py` (referee, 2026-09-16). The referee also read `recheck.py` line
by line against (V0)–(V3).

**Claim.** Let `R` be the set of the 211 words on the `REST` lines of
`research/artifacts/one-relator-linton-graph-certificates-scripts/census3_16.out` (md5
`26b721a1e47eedcbb971190afbe59991`). These are the length-16 unpeelable residue classes left by
`census3.py 16 16`. For every `w ∈ R` other than the 39 words listed below, the group
`G = <a, t | w>` has a subgroup `H` of index `k ≤ 8` with `H ≅ F_n ⋊ Z` for some `n` with
`3 ≤ n ≤ 79`. Hence `G` is residually finite, and so sofic.

The index, window span and fibre rank of each of the 172 words are listed in §2 of the
artifact.

**Coverage.** `lg_words16.out` splits `R` into 70 words ending `-> PASS` and 141 `NONFREE` words.
The 141 in turn split into:
- 34 words where this lane's transported Linton certificate passes (artifact §4, not landed);
- 107 words, called *open*, that no certificate in the repository covers.

None of the 141 `NONFREE` words has a landed Linton certificate, and 139 of them are in the
claim. The two left out, `TTTATAAtataaTAAA` and `TTTATAAtataaatAA`, have only the unlanded
transported certificate.

The 172 words of the claim are:
- all 107 open words, certified at index 2 (102 words), 4 (3), 5 (1) and 6 (1);
- 32 of the 34 transported-certificate words;
- 33 of the 70 `PASS` words.

**The 39 excluded words.** No certificate was found for these words within the searched range
(artifact §3). All 39 are covered by a Linton graph certificate.
- Two are transported-certificate words: `TTTATAAtataaTAAA`, `TTTATAAtataaatAA`.
- Thirty-seven are `PASS` words of `lg_words16.out`:
  - `TTTATATaaTAAttaa`, `TTTATATaatAATTaa`, `TTTATATaatAAttaa`, `TTTATAAtaTTAtATA`
  - `TTTATAAtataTattA`, `TTTATAtATATTatAA`, `TTTATAtATATaattA`, `TTTATAtaaTAATTaa`
  - `TTTATAtaatAATTaa`, `TTTATAttaaTAATaa`, `TTTATAttataTTAAA`, `TTTATAttataTatAA`
  - `TTTATAttataaTAtA`, `TTTAATTaaTAAtata`, `TTTAATTaatATATaa`, `TTTAATTaatATAtaa`
  - `TTTAATTaatAATata`, `TTTAATTaatAAtata`, `TTTAATTaatAtATaa`, `TTTAATTaatAtAtaa`
  - `TTTAATTatatAAtaa`, `TTTAATaTaTAAttaa`, `TTTAATaaTATAttaa`, `TTTAATaaTAAttata`
  - `TTTAATaaTAtAttaa`, `TTTAATaatAATTata`, `TTTAATataTAAttaa`, `TTTAAtaaTATAttaa`
  - `TTTAAtaaTAATTata`, `TTTAAttaaTAATata`, `TTATAAtaTTAttata`, `TTATAtATTatAtata`
  - `TTATAtATaTAttata`, `TTATAttaTTAAtata`, `TTATAttaTatAtata`, `TTATAttaaTAttata`
  - `TTAtATATaTATAtta`

Failing to find a certificate is not evidence against fibring: the search bounds the character
coefficients and the potentials, and the collapse search is greedy.

Letters: `A = a^{-1}` and `T = t^{-1}`. The claim concerns the listed relators as written. No
basis change or automorphic image is used.
