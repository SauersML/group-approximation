---
rg: 2
id: atlas-rank-five-complete-packet-exporter
kind: claim
title: The complete rank-five Atlas presentation packet has a deterministic sparse exporter
---

**ESTABLISHED.**
`experiments/atlas_relator_rank5_complete_packet.py` reconstructs the complete
rank-five Atlas presentation packet directly from the three proved source
generators:

```text
atlas_relator_rank5_full_family.py    4,612 distinct nonempty words
atlas_relator_rank5_involutivity.py      24 new words
atlas_relator_rank5_reverse.py           12 named entries
                                      -----
                                      4,648 presentation entries.
```

The exporter uses only sparse Atlas syllable lists and 4-by-4 binary matrices;
it does not allocate a regular `A8` matrix or any dense 20,160-dimensional
operator.  It preserves source order, writes JSON incrementally, and hashes the
canonical ordered word list.  Running

```text
python3 experiments/atlas_relator_rank5_complete_packet.py
```

audits the following complete ledger:

```text
100 involutivity relations considered
 12 freely trivial
 88 nontrivial, of which 64 duplicate the full family and 24 are new
  8 of the 12 reverse-dictionary relations freely trivial
  4 nontrivial reverse relations, all new
4,648 named presentation entries
4,640 reduced nonempty words, all distinct.
```

The ordered presentation-list SHA-256 is

```text
9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99.
```

Passing `--emit PATH` writes the complete JSON packet; passing
`--verify-source-kernels` additionally repeats the source scripts' exact
Leavitt-kernel checks.  The latter verification is deliberately separate from
the lightweight deterministic reconstruction because those exact checks were
already performed in the source claims.

This resolves the packet-provenance prerequisite of
`atlas-three-mode-balanced-area-table-export`.  It does **not** export the
balanced-area Laurent coefficients; that finite symbolic collector remains
the next step.
