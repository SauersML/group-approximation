---
rg: 2
id: canonical-trace-square-is-blind-to-iwahori-overlap
kind: claim
title: Canonical adjoint trace squares do not control the Iwahori projection overlap direction
artifacts:
  - research/artifacts/canonical-iwahori-one-overlap-audit-2026-08-21.md
distinct_from:
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that forces all group-word traces to be canonical while preserving an existing failure; this computes why the trace-square statistic misses the centered projection direction.
  trace-blindness-sharpness: that is a general normalized-HS visibility firewall; this gives the exact Iwahori block-flip calibration.
---

For `U in U(d)`, the normalized operator trace of conjugation on the
`d^2`-dimensional Hilbert--Schmidt space is

```text
tr_(End(M_d))(Ad_U)=|tr_d(U)|^2.                              (CTS1)
```

Thus canonical group traces make the AVERAGE adjoint trace vanish at every
nonidentity word, but they do not control one selected unit vector
`(P-tr(P)1)/sqrt(tr(P)(1-tr(P)))`.

The gap is sharp already in one `2m`-dimensional block.  Put

```text
P=diag(1_m,0_m),       U=[[0,1_m],[1_m,0]].                   (CTS2)
```

Then `tr(P)=1/2`, `tr(U)=0`, `U^2=1`, and

```text
UPU^*=1-P,
tau(PUPU^*)=0,
phi_P(U)=-1,
||[P,U]||_2=1.                                                (CTS3)
```

So even a half-dimensional physical projection and exact canonical
first-word trace can carry the maximal square-root odd mode.  Positive
physical density is still only one direction in the adjoint Hilbert space;
no inequality using `(CTS1)` alone can prove `(COH1)`.
