---
rg: 2
id: atlas-six-relator-o8m2-has-no-marked-pair
kind: claim
title: No marked A8 pair in O8-(2) satisfies the Atlas six-relator quotient
artifacts:
  - experiments/atlas_o8m2_six_relator_screen.py
  - experiments/atlas-six-relator-o8m2-screen.json
distinct_from:
  atlas-o8m2-packet-collision-exclusion: that imposes the full sixteen-edge packet and collision 19243; this tests only the five saturated boundary words and centrality word c_19243.
  atlas-six-relator-o8p2-has-no-marked-pair: that excludes the preceding plus-type orthogonal endpoint; this exhausts the single minus-type A8 class.
---

No pair of marked `A8` charts in `G=O8-(2)` satisfies

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1.                 (S6O8M-1)
```

There is one ambient `A8` class.  Its normalizer has order `120960`, its
centralizer has order three, and the quotient normalizer/centralizer has
order `40320=|Aut(A8)|`; hence one relative-conjugator screen includes the
graph-outer marking.

The exact first-relator seed partition gives

```text
class(x)       C_G(x)    class hits     conjugators
   1071         184320        15          2764800.    (S6O8M-2)
```

Literal multiplication of the remaining five frozen words has first-failure
census

```text
s_11       s_30       s_44       s_55       c_19243       survive
2762496     2112        168         21           3             0. (S6O8M-3)
```

Thus exactly three marked conjugators satisfy all five boundary words, and
the interior centrality word rejects all three.

## Exact certificate

The script uses the degree-119 primitive permutation model, the unique
normal `A8` inside `(3 x A8):2`, and an exact `GL4(2)` marking.  The word
`s_0` has the pinned form `x A x C x D`.  It enumerates the ambient
conjugacy class of `x`; for every class element satisfying that equation it
replays the complete centralizer coset.  These fibers partition every
ambient conjugator satisfying `s_0`, so the screen is exhaustive rather
than sampled.  All group and word operations are exact GAP permutation
arithmetic.

