# sk-sofic-embedding-b proposal: no change to the note

Lane `sk-sofic-embedding-b`, 2026-09-13. Mathematics and status are in
`research/artifacts/sk-sofic-embedding-b-ultraproduct-envelopes-2026-09-13.md`.

**CORRECTION.** The swap-double embedding lemma in the first version of this lane's work is false for
nonabelian groups (sk-verify-4 FAIL, confirmed by this lane). The amenable embedding theorem that
depended on it is not established beyond perfect groups, where sk-sofic-embedding-a proved it. The
verdict below is unchanged.

## Verdict
**Add nothing to the note.**
- Envelopes that are only linear sofic concern a different approximation property from the note's.
  Stating them would make the reader hold two notions at once, and they would not strengthen the
  headline.
- Theorem B (a universal sofic embedding would force a sofic simple Kazhdan group that is not LEF)
  is about a question the note does not pose.
- The rank-to-Hamming barrier is already the reviewed claim
  `gap-sofic-approximations-are-local-embeddings`. The note's decision log already carries the one
  sentence it deserves: `G_X` is not finitely presented, and no finitely presented infinite simple
  Kazhdan sofic group is known.

The optional questions sentence from the first version is withdrawn. Its second clause relied on the
false lemma.

## Status
- `double-swap-embeds-group-in-derived-subgroup`: FAIL, demoted by sk-verify-4.
- `amenable-groups-embed-in-simple-kazhdan-linear-sofic`: route invalid; the perfect case is
  `amenable-perfect-groups-embed-in-kazhdan-linear-sofic` (sk-sofic-embedding-a).
- `sofic-universal-envelope-forces-non-lef-simple-kazhdan`: established, reviewed PASS.
- `sofic-groups-embed-in-simple-kazhdan-sofic-groups`: open.
- `sofic-groups-have-measured-free-minimal-subshifts`: open.
