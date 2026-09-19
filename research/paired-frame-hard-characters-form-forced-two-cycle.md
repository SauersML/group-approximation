---
rg: 2
id: paired-frame-hard-characters-form-forced-two-cycle
kind: claim
title: Every paired-frame edge isomorphism swaps the two hard characters
artifacts:
  - experiments/schur_packet_paired_commutant_frame.py
  - experiments/schur_packet_frame_transport_cycles.py
distinct_from:
  support-packet-paired-word-frame-exposes-forbidden-rank: that proves every edge isomorphism sends 101 to 011; this computes the reverse image too and proves that the hard pair is a forced two-cycle for all 32 isomorphisms.
  one-sided-paired-frame-reverse-reservoir-collapse: that must attach an infinite level coordinate to the finite edge; this proves no choice among the finite edge maps can itself make the reverse reservoir transient.
---

For the plus and minus order-128 frame groups in `(PWF1)`, every one of the
32 changes of four noncentral generators which induces an edge-group
isomorphism acts on the hard central characters by

```text
101 <--> 011.                                             (H2C1)
```

There are eight full character-transport permutations, each realized by
four generator changes.  Although their actions on the other six characters
differ, all eight contain the transposition `(101 011)`.  Consequently:

1. changing the finite edge isomorphism cannot lengthen the hard return time;
2. alternating different finite edge isomorphisms still returns `011` to
   `101` at the next compatible plus-to-minus transport; and
3. every successful orientation must couple `(H2C1)` to an infinite label
   such as a prefix, valuation degree, or coset site.

In particular, the reverse reservoir is not merely one of several possible
finite leaks.  It is the unique compulsory partner of the forbidden
character, with exact return time two after forgetting any infinite label.

There is no finite automorphism-reset loophole. By
`closed-covariant-reynolds-cycle-has-full-overlap`, a reset which renames the
reverse character also transports the entire reverse frame. Closing that
framed cycle returns the complete Reynolds projection and therefore has full
overlap, rather than the local `1/98` deficit.
