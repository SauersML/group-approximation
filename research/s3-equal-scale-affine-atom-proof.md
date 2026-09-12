---
rg: 2
id: s3-equal-scale-affine-atom-proof
kind: route
title: Use the rank-four radical sector and the balanced Pauli half in the rank-six sector
target: s3-active-complement-is-three-equal-scale-affine-atoms
requires:
  - six-generator-one-jump-router-has-s3-radical-atlas
artifacts:
  - experiments/s3_equal_scale_active_atoms.py
  - experiments/s3-equal-scale-active-atoms.json
---

The central-character ranks in `(SRA4)` are four on `(K,J)=(+1,-1)` and six
on `(K,J)=(-1,-1)`.  The standard class-two packet decomposition therefore
has four-dimensional simples in the first sector and one eight-dimensional
spin simple in the second sector, with arbitrary external multiplicities.

On the rank-four sector, every word in `(SRA6)` lies in the radical.  It acts
scalarly on each simple, so either `b`-eigenspace is a direct sum of
four-dimensional simples.  This proves the divisibility assertion for
`P_(+,+)` and `P_(+,-)`.

On the rank-six sector the commutator form is nondegenerate.  The chosen
nonzero endpoint word `b` is therefore noncentral modulo `<J,K>`.  Hence
there is a packet word `c` with

```text
[b,c]=J
```

on that sector.  Since `J=-1`, `c` exchanges the `+1` and `-1` eigenspaces
of `b`.  They consequently have equal dimension four in every eight-
dimensional spin simple and equal rank after arbitrary multiplicity.  This
proves `(SEA3)`.  The projection identities in `(SEA2)` are the four-atom
Boolean partition of the commuting involutions `(J,K,b)`.
