---
rg: 2
id: s3-radical-affine-contexts-have-five-fourths-floor
kind: claim
title: Two S3 radical bits give an exact five-fourths three-context failure floor
artifacts:
  - experiments/s3_radical_context_router_search.py
distinct_from:
  robust-rank-one-endpoint-marginal-floor: that gives a universal lower bound of one carrier mass from shared marginals; this computes the stronger exact profile of the six-generator radical packet.
  six-generator-one-jump-router-has-s3-radical-atlas: that constructs the packet and radical orbit; this chooses concrete endpoint bits and computes their contextual failure projections.
---

On a `K=J=-1` simple of the six-generator packet, the commuting radical words
in `(SRA6)` have joint spectrum

```text
R={000,011,101,110}                                    (RAF1)
```

with equal trace on all four atoms.  Let `u` and `v` be the last two
coordinates on `R`.  Use `u` at both endpoints of the `00` context, use `v`
at both endpoints of the `11` context, and use `(u,v)` in the crossed `01`
context.  With the failure convention of `(RRF1)`, the masses on a carrier of
mass `s` are

```text
p_00=s/2,             p_01=s/4,             p_11=s/2,
p_00+p_01+p_11=5s/4.                                (RAF2)
```

The four radical atoms have failure triples

```text
000:(1,0,1),   011:(0,1,0),
101:(0,0,1),   110:(1,0,0).                           (RAF3)
```

Thus each context occupies at most one source copy, while their total has a
strict `1/4` slack over the universal rank-one floor.

Exhaustion over all six nonconstant affine bits on `R` and all `6^3`
coordinate-permutation transports finds no nondegenerate atlas whose failure
count is exactly one at every atom.  The minimum total count is five, with
maximum pointwise count two, and `(RAF2)--(RAF3)` have minimum word and
transport complexity.  The verifier checks all `233280` nondegenerate
candidate atlases.

The floor concerns analytically compressed block mass.  It does not by itself
place those three block spaces in recurrence grandchildren or E5 boundary
layers.
