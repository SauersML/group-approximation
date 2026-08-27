---
rg: 2
id: atlas-a4-packet-letters-generate-both-a8-charts
kind: claim
title: The thirty shortest A4 contexts use one diameter-nine generating alphabet for both A8 charts
artifacts:
  - experiments/atlas_a4_packet_generation.py
---

Take the thirty shortest pair-cubes of `atlas-shortest-a4-triangle-packet`.
For each chart factor separately, collect the distinct chart elements which
occur as one of the two repeated letters in those contexts.  The two resulting
sets are in fact the **same ten matrices** in `GL(4,2)`, consisting of six
order-three and four order-two elements.

That common ten-letter alphabet generates the entire chart group

```text
GL(4,2) ~= A8
```

of order `20160`.  Moreover its directed Cayley graph has exact diameter nine:
every chart element is a positive word of length at most `9` in the packet
letters, and some elements require length `9`.  Exact closure gives

```text
|<packet letters in factor 1>| = 20160,
|<packet letters in factor 2>| = 20160,
diam_S(A8) = 9.                                        (A4-PACKET-GEN)
```

Thus the thirty A4 contexts are globally spanning on **both** chart sides with
a quantitatively short common compiler alphabet.  Any agreement theorem which
synchronizes the local chart actions on every packet letter automatically
controls the complete A8 actions; there is no unseen chart subgroup on which a
high-dimensional alignment can escape.