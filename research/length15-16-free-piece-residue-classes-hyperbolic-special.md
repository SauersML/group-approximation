---
rg: 2
id: length15-16-free-piece-residue-classes-hyperbolic-special
kind: claim
title: All 30 length-15 unpeelable one-relator classes and 70 of the 211 length-16 classes are hyperbolic and virtually special
distinct_from:
  row29-one-relator-group-is-hyperbolic-and-virtually-special: that settles the single length-15 class row 29 by hand; this certifies every length-15 residue class and 70 length-16 classes by the general certificate.
  unpeelable-extreme-one-relator-groups-sofic: that is the open soficity claim for all unpeelable relators; this proves hyperbolicity and virtual specialness for an explicit finite list of them.
- research/artifacts/one-relator-linton-graph-certificates-scripts/lintongraph.py
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_l15.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_seq16.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_words16.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/census3_16.out
---

**ESTABLISHED** through `length15-16-free-piece-residue-via-linton-certificates` (computer-checked,
not independently reviewed).

**Claim.** Each of the following two-generator one-relator groups `<a, t | w>` is hyperbolic,
contains no Baumslag–Solitar subgroup, and is virtually special:
1. the 30 classes of the length-15 unpeelable residue (the `REST` lines of
   `research/artifacts/or-length15-residue-scripts/residue-output.txt`), row 29 included;
2. 70 of the 211 classes of the length-16 unpeelable residue that remain after the partial-positivity
   search of `census3.py 16 16`: 44 with an exponent sum equal to zero and 26 with both exponent sums
   nonzero. They are the lines ending `-> PASS` in `lg_words16.out`.

The other 141 length-16 classes are not covered: in every zero-exponent basis tried, their Magnus
rewriting has no interior letter occurring exactly once, so the Magnus piece is not visibly free.

No novelty is claimed for the method; the census lists are the repository's own.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/one-relator-linton-graph-certificates-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
