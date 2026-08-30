---
rg: 2
id: atlas-rank-five-complete-packet-exporter-proof
kind: route
title: Reconstruct and hash the complete rank-five packet sparsely
target: atlas-rank-five-complete-packet-exporter
requires:
  - atlas-steinberg-rank-five-translation
artifacts:
  - experiments/atlas_relator_rank5_complete_packet.py
  - experiments/atlas_relator_rank5_full_family.py
  - experiments/atlas_relator_rank5_involutivity.py
  - experiments/atlas_relator_rank5_reverse.py
---

The exporter invokes the three exact source generators certified by the
rank-five translation theorem, preserves their source order, and keys every
reduced word by its factor labels and canonical `4 by 4` binary matrices.  It
therefore detects both free triviality and every cross-source collision
without constructing the regular representation of `A8`.

An independent run reproduced all internal assertions:

```text
4,612 full-family nonempty words, all distinct;
100 involutivity words: 12 trivial, 64 duplicates, 24 new;
12 reverse-dictionary entries: 8 trivial, 4 nontrivial and new;
4,648 named presentation entries;
4,640 reduced nonempty words, all distinct.
```

The canonical ordered sparse word list has SHA-256

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99.
```

Serialization is incremental and contains only sparse Atlas syllable lists
and binary `4 by 4` matrices.  The asserted collision ledger, counts, source
labels, and ordered hash make the emitted packet a deterministic
reconstruction of the proved presentation packet.
