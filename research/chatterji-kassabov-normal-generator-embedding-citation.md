---
rg: 2
id: chatterji-kassabov-normal-generator-embedding-citation
kind: route
title: Import Chatterji-Kassabov Theorem 3
target: chatterji-kassabov-normal-generator-embedding
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Citation import.  Chatterji--Kassabov, arXiv:2601.22907, Theorem 3, read
verbatim from the paper's HTML on 2026-08-17 together with Lemma 4, Remark 5
and the proof of Lemma 4; the quotations are in
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.1.

Not reproved here and no Lean counterpart exists.  This is the most recent
and least settled input in the region — a January 2026 preprint — and it is
the single citation on which all four live routes into
`boone-higman-conjecture` depend.

## Trust surface

If Theorem 3 were withdrawn or weakened, the entire near-solution goes with
it: `proper-normal-subgroups-miss-the-normally-generating-core` and
`every-nontrivial-core-element-normally-generates-the-envelope` are stated as
conditionals about *any* simple-core-plus-normal-generator pair and would
survive as vacuous, but nothing would exhibit such a pair, and the routes
would have no envelope to work on.

Two components could fail independently and are worth naming: the ring
extension (their Lemma 4, whose proof this audit read in full and found
sound) and the property-(T) plus finite-presentation packaging (Shalom,
Krstić--McCool, neither re-read here).  Only the first is used by
`universal-sandwich-ring-is-finitely-presented-and-injective`; the second is
what that node makes unnecessary.
