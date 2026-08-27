---
rg: 2
id: atlas-a4-rank-three-core-proof
kind: route
title: Exact packet pruning and exhaustive automorphism audit prove the rank-three core theorem
target: atlas-a4-rank-three-core
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-19243-s3xs3-localization
  - atlas-a4-19243-parabolic-subgroup-ladder
artifacts:
  - experiments/atlas_a4_rank_three_core.py
---

The exact script reconstructs all thirty radius-five pair-cubes.  From the
large component it computes `Z(H_18)` and removes precisely those words whose
order-three label is one of the two nonidentity central elements.  Direct
counting gives

```text
14 retained words,
16 discarded words,
8 distinct retained involution/order-three pairs,
8 distinct retained oriented pairs.
```

The retained simple graph has two connected components.  In each component it
finds two involution labels, two order-three labels, seven word occurrences and
all four possible distinct pairs.  Hence each component graph is `K_(2,2)`.
Exact subgroup closure gives order six for both components.  By the established
localization these are `H_6` and `K`.  Closure of their union has order `168`,
and every one of its matrices fixes the last basis vector and covector.  The
parabolic-ladder theorem therefore identifies it with the standard
`diag(GL_3(F2),1)` subgroup.

For the classical statement the script exhausts all `20160` inner alignment
matrices and all `20160` outer-twisted alignments.  In each coset it records the
survivors of the fourteen-word core and of all thirty packet words.  The two
survivor lists agree **element for element** and have size thirty.  It then
evaluates the exact stored collision `q_19243` on those alignments and finds no
survivor in either coset.  Thus `(A4-CORE-CLASSICAL)` is an exact finite audit,
not a numerical observation.

Finally the standard rank-three `H` here is exactly the `H=GL_3(2)` used in the
raw-S3 localization underlying `atlas-two-s3-covariance-collapse`; its two
named covariance generators belong to `H` by construction.  Hence closeness of
the relative chart frame to `lambda(H)'` would indeed collapse those two
covariance coordinates without requiring full `A8` centrality.
