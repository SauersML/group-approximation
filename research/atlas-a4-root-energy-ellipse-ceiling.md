---
rg: 2
id: atlas-a4-root-energy-ellipse-ceiling
kind: claim
title: One ellipsoidal scalar in square-root four-cycle energies beats the 19243 wall
distinct_from:
  atlas-a4-joint-weighted-cycle-ceiling: that target leaves five positive weights existentially quantified; this target analytically eliminates all of them and retains only one nonlinear scalar of the four trace deficits.
  atlas-a4-anisotropic-four-cycle-ceiling: that target uses a fixed diagonal Cauchy budget; this target uses the exact triangle envelope and the optimized weighted S3 exchange rate.
---

For the normalized exact-regular A4 context-network sequence put

```text
x_ij(n)=sqrt(1-Re tau_n(V_n(tij))) >=0,
S_n=2x_01(n)+2x_23(n)+4x_30(n).
```

Prove the single scalar ceiling

```text
limsup_n [S_n^2 + S_n x_12(n) + x_12(n)^2] < 3/512.   (A4-ROOT-ELLIPSE)
```

This is the completely optimized form of the four-cycle-to-S3 contradiction.
Indeed `S_n^2` is the exact positive-word triangle upper budget for the
synthesized raw involution `t21`, while `x_12^2` is the budget for the directly
observed raw involution `t12`.  The cross term is precisely what remains after
optimizing the relative weights in the two-generator S3 Cayley gap.

Equivalently,

```text
S_n^2+S_n x_12+x_12^2
 =(S_n+x_12/2)^2 + 3x_12^2/4,
```

so the target is literally membership in one fixed ellipse in the two aggregate
root-energy coordinates `(S_n,x_12)`.

## Attempts

- **Search the ellipse directly.**  Do not introduce artificial Cauchy or S3
  weights in an SDP/SOS implementation.  Lift the four nonnegative root-energy
  variables and optimize this one positive quadratic form.
- **Exploit direction-selective collision control.**  A strong bound on `t30`
  is especially valuable because it enters `S_n` with coefficient `4`; `t01`
  and `t23` enter with coefficient `2`, while `t12` occupies the separate
  detector coordinate.
- **Use the two-context classical core as a dual guide.**  The exact packet
  audit already identifies two A4 contexts hitting every collision-perfect
  classical alignment.  Ask whether their matrix-valued residuals dominate the
  ellipse rather than reconstructing all thirty context gauges.
- **Return the escaping point.**  Failure of a finite SOS relaxation should
  output an approximate point `(S,x12)` outside the ellipse together with the
  multiplicity mode realizing it; that is a targeted new packet-search input.