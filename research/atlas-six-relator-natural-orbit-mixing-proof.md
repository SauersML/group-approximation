---
rg: 2
id: atlas-six-relator-natural-orbit-mixing-proof
kind: route
title: Replay the exact small natural-chart census component by component
target: atlas-six-relator-natural-orbit-mixing-floor
requires: []
artifacts:
  - experiments/atlas_six_relator_blockwise_audit.py
  - experiments/atlas-six-relator-blockwise-audit.json
---

The attached exact audit evaluates the literal six words on aligned,
one-chart-trivial, and every marked two-chart natural action through degree
eleven.  The aligned chart is the unique five-row survivor and
`c_19243` is a nonidentity involution there; the asymmetric charts fail
`s_0` or `s_11`.

On any generated permutation component of size at most eleven, simplicity
of `A8` makes each chart restriction trivial or injective.  Under the
claim's orbit hypothesis an injective restriction is one natural
eight-point orbit plus fixed points, hence is one of the audited cases after
padding by fixed points.  All nontrivial cases fail, so both restrictions
are trivial on the component.  This is exactly the claimed componentwise
mixing floor.
