---
rg: 2
id: quantitative-hs-stability-for-slofstra-zhang-pictures
kind: claim
title: Upgrade high-girth phase pictures to a normalized-HS curvature inequality
distinct_from:
  slofstra-zhang-high-girth-phase-survival: that excludes exact nonzero-phase pictures; this must start from approximate unitary relations and produce a dimension-free energy lower bound.
  s3-radical-charts-give-linear-local-hs-payment: that charges a finite chart mismatch once supplied; this must force such mismatch or energy from the global two-dimensional return cells.
---

For a fixed high-girth finite incidence complex carrying the S3 radical
charts, prove constants `c,C>0` such that every finite-dimensional unitary
assignment satisfies

```text
marked phase mass <= C * total normalized-HS relator energy
```

or, in the localized form needed by the return transducer, every nonzero
phase carrier either returns with the prescribed fresh-context type or pays
at least `c` times its normalized Hilbert mass in cell-relator energy.

The constants must be independent of ambient matrix dimension and of the
computation level represented by the return cell.

## Attempts

- Minimal-picture reductions and Euler's formula prove the zero-energy case
  only.  An almost representation need not determine a finite planar diagram,
  so counting exact cells does not yield the inequality.
- Finite-group exactification controls each vertex chart, but the obstruction
  lives in the two-dimensional gluing.  A proof likely needs a cosystolic or
  operator-valued small-cancellation estimate for the whole complex.
