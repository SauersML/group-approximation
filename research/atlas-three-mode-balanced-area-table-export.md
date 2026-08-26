---
rg: 2
id: atlas-three-mode-balanced-area-table-export
kind: route
title: Stream the rank-five packet through sparse label and Weyl normal forms
target: atlas-three-mode-balanced-area-coefficient-table
requires:
  - atlas-steinberg-rank-five-translation
  - atlas-three-label-mode-two-unitary-moment-reduction
  - atlas-rank-five-complete-packet-exporter
---

The first serialization step is complete in
`atlas-rank-five-complete-packet-exporter`.  It preserves the twelve named
reverse-dictionary entries

```text
g w_g^(-1)
```

already constructed and verified by
`experiments/atlas_relator_rank5_reverse.py`, and merges them with the 4,636
full-family and involutivity words.  Eight reverse entries reduce freely to the
empty word, so downstream collection may skip them after checking the recorded
4,648-entry / 4,640-nonempty ledger.

For each word, stream formula `(TLMP1)` one syllable at a time.  Expand each
of the fixed label projections

```text
P_0=E,
P_1=(I+W)/2-E,
P_2=(I-W)/2
```

in the sparse basis `I,W,E`.  Products of left translations and `W` remain
permutation operators in the finite semidirect label action; inserting `E`
turns a segment into a rank-one matrix unit, whose subsequent products and
trace are computed by endpoint matching.  In parallel normalize every
coefficient word to

```text
t^A S^a D^b,
```

combining equal `(label state,a,b,A)` keys after every syllable.  At the end,
discard `a!=0` or `b!=0`, take the exact normalized label trace, and collect
the result by `A`.  This yields `(BAT1)` without enumerating the formal
`3^(2l)` sector expansion or allocating dense label matrices.

Validate on three controls before the full packet: the empty word gives
`f=1`; a one-chart nonidentity word gives `f=0` under the regular label
trace; and the `z->1` specialization agrees with the previously established
small-phase/commutative evaluation.  The final artifact should include a
hash of the regenerated `T_St` word list so the Laurent table is tied to the
proved usable packet.
