---
rg: 2
id: mf-recognition-recursive-presentations-is-second-level-complete
kind: claim
title: MF and non-MF recognition are exactly second-level complete for recursive presentations
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that is the finite-presentation upper bound; this supplies matching FIN and INF hardness on infinitely generated recursively presented groups.
  mf-recognition-finite-presentations-is-pi2-complete: that transports this recursive hardness through the finite-CEP graph witness and tensor-synchronized Higman rope.
---

For the natural effective coding of countably generated recursively presented
groups,

```text
NONMF_rec is Sigma^0_2-complete,
MF_rec    is Pi^0_2-complete.
```

The hardness reduction is uniform and uses only one fixed finitely presented
non-MF group.  The upper-bound certificate argument applies unchanged to a
recursive relator stream after adding the relator-prefix index to the scale.
This statement does not assert anything about finite-presentation hardness.
