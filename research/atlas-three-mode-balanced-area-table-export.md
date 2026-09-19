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
  - atlas-three-mode-balanced-area-sparse-collector
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

`experiments/atlas_three_mode_balanced_area.py` now carries out the following
exact collection.  For each word, stream formula `(TLMP1)` one syllable at a
time.  Expand each
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

The implementation validates five exact controls before the full packet: the
empty word gives `f=1`; a nonidentity word in either chart gives `f=0`; the
second-chart identity gives `f=1`; and a second-chart word followed by its
inverse gives `f=1`.  The final artifact includes the hash of the regenerated
`T_St` word list so the Laurent table is tied to the proved usable packet.

The first local nonempty-word calibration is already about 23 seconds, so the
complete packet is a remote/MSI job rather than a local run.  The script has a
hard live-state cap and prints the exact remote command on overflow.  It also
maintains the incremental gcd of `f_s(t)-1` and a checked Bezout certificate,
so a negative decision may stop before exporting the rest of the packet.

The completed exact run stopped rigorously after the first row, as the target
claim explicitly permits for a negative decision.  It found

```text
f_(root_12_1e)(t)   = 16953689/41287680,
f_(root_12_1e)(t)-1 = -24333991/41287680.
```

The constant multiplier `-41287680/24333991` gives Bezout identity `1`, so
the running Laurent-polynomial gcd is exactly `1` and no common nonzero root
exists.  The packet hash is the exporter hash above; peak sparse state count
was `30,812`.  The checked JSON and execution log are
`experiments/atlas-rank5-balanced-area.json` and
`experiments/atlas-rank5-balanced-area-17081560.log`.  A fresh local replay
reproduced the JSON byte for byte.
