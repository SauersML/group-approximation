---
rg: 2
id: leavitt-d3-affine-two-carrier-transport-is-absent
kind: claim
title: No affine two-carrier length-thirteen word gives direct Leavitt transport
artifacts:
  - research/leavitt-d3-affine-two-carrier-transport-is-absent-proof.md
  - research/artifacts/search-degree3-repeated-carrier-transport.py
  - research/artifacts/search-degree3-repeated-carrier-transport.sbatch
distinct_from:
  leavitt-transport-drift-and-l7-atomic-no-go: that exhausts the minimal length-seven atomic alphabet; this treats the higher-valence length-thirteen topology with repeated formal compound carriers and recognizes whole ordered transport relators.
---

For every degree-three length-thirteen sign path of orbit-valence type
`(1,5,7)`, place the four gates `a,b,c,d` at any four cyclic sign changes.
Fill all remaining slots by either of two formal compound carriers `x,y`
according to any linear Boolean function of cyclic parity, the adjacent signs,
and the height residue modulo three.

After solving the unary orbit, none of the `13,478,400` resulting systems has
its two ordered residual relators simultaneously of the form

```text
a U c U^(-1),        b U d U^(-1)
```

up to cyclic rotation, swapping source or target gates, and changing the two
coefficient-copy indices.  Thus this entire repeated-carrier design class
cannot transport `[a,b]=1` to `[c,d]!=1`.
