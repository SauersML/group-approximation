# sk-sofic-embedding-b proposal: no change to the note

Lane `sk-sofic-embedding-b`, 2026-09-13. Mathematics and status:
`research/artifacts/sk-sofic-embedding-b-ultraproduct-envelopes-2026-09-13.md`.

## Verdict
**Add nothing.** Nothing this lane proved belongs in the note, for reasons that are reader-facing:

- **Theorem A** (every finitely generated amenable group embeds in an infinite simple Kazhdan
  `F_q`-linear sofic group) is about a different approximation property from the note's. The note is
  about groups that are sofic and hyperlinear; an envelope that is only linear sofic would make the
  reader hold two notions at once and would weaken, not strengthen, the headline. It also needs a
  free minimal subshift over an arbitrary amenable group, a Folner rank model and a Whitehead
  identity, none of which the note otherwise carries. Its place is the graph.
- **Theorem B** (a universal sofic embedding would force a sofic non-LEF simple Kazhdan group) is a
  statement about a question the note does not pose.
- The **rank-to-Hamming barrier** is already the reviewed claim
  `gap-sofic-approximations-are-local-embeddings`, and the note's decision log already carries the
  one sentence it deserves, in decision 8: `G_X` is not finitely presented, and no finitely presented
  infinite simple Kazhdan sofic group is known.

## If a questions paragraph wants one more line
Decision 18 keeps two questions, so this is offered only as a replacement candidate, not an addition.
The sharpest form of this lane's target, in the note's voice:

```latex
We also do not know whether every finitely generated sofic group embeds in an infinite simple
Kazhdan group that is sofic; for amenable groups there is such an embedding into a group that is
linear sofic.
```

Cost: 3 lines, no new citation. Reader trade-off: it names the natural strengthening of the theorem
and says how far it is proved, but it introduces linear soficity, a notion the note never uses. This
lane recommends against it.

## Status
- `double-swap-embeds-group-in-derived-subgroup` (+ proof): established, unreviewed.
- `amenable-groups-embed-in-simple-kazhdan-linear-sofic` (+ proof): established, unreviewed.
- `sofic-universal-envelope-forces-non-lef-simple-kazhdan` (+ proof): established, unreviewed.
- `sofic-groups-embed-in-simple-kazhdan-sofic-groups`: open, with attempts.
- `sofic-groups-have-measured-free-minimal-subshifts`: open, with attempts.
- Review queued with sk-verify-4.
