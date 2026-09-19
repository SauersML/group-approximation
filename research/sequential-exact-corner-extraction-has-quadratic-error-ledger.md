---
rg: 2
id: sequential-exact-corner-extraction-has-quadratic-error-ledger
kind: claim
title: Sequential approximate corner extraction has a quadratic dimension ledger
artifacts:
  - research/artifacts/microscopic-schreier-extraction-dimension-ledger-2026-09-05.md
distinct_from:
  orthogonal-frozen-support-surgery-has-square-root-rank-cost: that assumes exact reducing cuts and sums independently supplied smooth changes; this starts from approximate retained-column intertwiners and controls all complementary polar corrections by their quadratic trace deficiencies.
  moving-subgroup-schreier-correction-has-no-index-loss: that constructs a correcting corner from spectral or Schreier data; this combines an arbitrary finite number of such corners with no error factor for the number of extractions.
---

Let U^(0) be a unitary generator tuple on H_0=C^d. At step i split
`H_i=P_i H_i direct_sum H_(i+1)`, where r_i=rank P_i>0, and suppose
rho_i is an exact representation on P_i H_i. With J_i the inclusion,
assume for every generator s

```text
||U_s^(i)J_i-J_i rho_i(s)||_HS<=xi_i sqrt(r_i).          (SEL1)
```

Let U_s^(i+1) be a unitary polar completion of the compression of
U_s^(i) to H_(i+1). Inverse symbols can be chosen compatibly. The
projections need not reduce U^(i) exactly and their ranks can be one.

For any finite number N of steps, use the resulting orthogonal blocks
in the original coordinates and define

```text
V_s=direct_sum_(i<N) rho_i(s) direct_sum U_s^(N).
```

Then each generator satisfies

```text
||U_s^(0)-V_s||_HS^2<=3 sum_(i<N) xi_i^2 r_i.          (SEL2)
```

Filling the final remainder by the trivial representation gives a
genuine representation alpha on C^d with

```text
||U_s^(0)-alpha(s)||_HS^2
 <=3 sum_(i<N) xi_i^2 r_i+4 dim H_N.                   (SEL3)
```

The norms here are unnormalized; divide the squared estimates by d
for the original normalized HS error. There is no factor depending on
N or on the smallest rank fraction. In particular, uniformly vanishing
xi_i and a vanishing final rank fraction give a full correction even
when every individual extracted corner has vanishing relative rank.
This conclusion assumes such a finite extraction schedule is supplied;
it does not assert that qualitative seed existence keeps all subsequent
residual errors small enough to continue that schedule.

DERIVATION
sequential-corner-trace-deficiency-proof
