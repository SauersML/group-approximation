---
rg: 2
id: leavitt-degree4-five-corner-omega-transport
kind: claim
title: A degree-four five-corner packet word transports the Leavitt Omega mismatch
artifacts:
  - research/artifacts/search-degree4-five-corner-omega.py
  - research/artifacts/search-degree4-five-corner-omega.sbatch
refuted_by: leavitt-degree4-five-corner-full-packet-is-absent
---

There is a placement of the immutable Leavitt packet
`(r,e,a,c,b,d,p)` and five identity slots in one of the two length-twelve
degree-four sign topologies

```text
-+-++-+-++++          -+-+++-+-+++
```

such that the two unary and two five-corner Reidemeister--Schreier relators,
after an exact unary pivot, make the quotient of the ordered residual
relations conjugate to `Omega(c,p)`.

## Attempts

The strict length-eight four-cycle is impossible by
`leavitt-degree4-strict-omega-four-cycle-no-go`.  Making all eight singleton
separators trivial in the first length-twelve topology merely pads the
positive diagonal word `t A t B t C t`; it is not a five-corner core.  The
attached exhaustive packet screen therefore retains the exact cyclic word,
allows identities only as part of the enumerated layout, and accepts solely
after complete ordered Bergman-normal-form pivot and target checks.  MSI job
`16662164` completed all 128 shards.  No layout even passed the second-unary
compatibility test, so this finite design class is refuted by the cited
claim.
