---
rg: 2
id: steinberg-zero-plane-transfer-closes-p-five
kind: claim
title: Projective plane transfer closes the zero-marginal recurrence in characteristic five
artifacts:
  - research/steinberg-p-five-zero-marginal-proof.md
distinct_from:
  steinberg-zero-marginal-recurrence-is-zero-at-p-three: this proves the analogous prime-five case by a plane-transfer orbit rather than characteristic-three fiber coincidence.
---

**ESTABLISHED.**  Over `F_5`, every zero-marginal common solution of the
two Steinberg chord Fox rows is zero.  More generally, a full zero plane
`b=B` can be transported between the planes

```text
b=4B                    and   b=4B/(1-4B),             (SPT1)
```

with the `4B=1` value handled by the point-exceptional branch.  Starting
from the uniform zero plane `B=-1`, this reaches every nonzero element of
`F_5`.  The plane marginal then kills `b=0` for `c!=0`, and the source
identity kills the remaining `c=0` values.

DERIVATION
steinberg-p-five-zero-marginal-proof
