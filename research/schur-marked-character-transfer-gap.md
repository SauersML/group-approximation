---
rg: 2
id: schur-marked-character-transfer-gap
kind: claim
title: The marked Schur central-character transfer contracts its transverse sector by one fifth
artifacts:
  - experiments/schur_marked_transfer_spectrum.py
  - experiments/schur-marked-transfer-spectrum.json
distinct_from:
  symmetrized-reset-collapses-schur-flow-to-one-ray: that identifies the stationary ray of the full reset type cone; this computes the exact spectral gap on the four marked central characters only.
  bass-serre-schur-transfer-contraction: that asks for contraction of the complete induction/restriction type operator with leakage accounting; this finite computation does not control hidden irreducible multiplicities.
---

For the support packet with central basis `(J,z_e,z_f)`, average the
contragredient character transports over all packet-pivot-compatible
involutions in `GL(3,2)` that fix the central mark `J`.  There are exactly ten.
On the four characters with `J=-1`, in the order `100,101,110,111`, the exact
transfer matrix is

```text
T = (1/5) * [[2,1,1,1],
             [1,2,1,1],
             [1,1,2,1],
             [1,1,1,2]].
```

Hence constants have eigenvalue `1` and the three-dimensional zero-sum sector
has eigenvalue, singular value, and spectral radius exactly `1/5`.

This passes the cheapest proposed nonamenability test at the marked
central-character level.  It does not yet pass it for the complete packet
type space, where stationary regular multiplicity flow may remain.
