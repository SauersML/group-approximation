---
rg: 2
id: atlas-rank-five-complete-packet-export-proof
kind: route
title: Reassemble and hash the three proved rank-five packet families
target: atlas-rank-five-complete-packet-exporter
requires:
  - atlas-steinberg-rank-five-translation
artifacts:
  - experiments/atlas_relator_rank5_complete_packet.py
---

`atlas-steinberg-rank-five-translation` identifies the complete usable packet
as the full Steinberg family, the missing involutivity entries, and the twelve
named reverse-dictionary entries.  The three exact source generators are
imported directly by `atlas_relator_rank5_complete_packet.py`; no generated
intermediate file is trusted.

The exporter serializes a word as its ordered list of chart indices and
`4 by 4` binary matrices.  It inserts the 4,612 distinct full-family words,
then scans all 100 involutivity relations.  Twelve are freely trivial and 64
of the remaining 88 duplicate full-family words, so precisely 24 new words
are inserted.  Finally it appends all twelve named reverse entries, including
the eight which reduce freely to the empty word because they remain distinct
presentation entries.  The four nonempty reverse entries are new.  Therefore
the ledger has

```text
4,612 + 24 + 12 = 4,648 presentation entries,
4,612 + 24 +  4 = 4,640 distinct nonempty reduced words.
```

All equality and reduction tests are exact on sparse binary matrices.  The
script asserts every count above, preserves source order, and hashes the
canonical JSON serialization of the ordered word list.  Re-execution gives

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99.
```

Thus it is a deterministic sparse exporter for exactly the proved complete
packet.  It never constructs a regular `A8` operator or a dense
20,160-dimensional matrix.
