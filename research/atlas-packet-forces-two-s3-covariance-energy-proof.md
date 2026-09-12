---
rg: 2
id: atlas-packet-forces-two-s3-covariance-energy-proof
kind: route
title: Compose the 19243 distance wall with sharp S3 Reynolds-Poincare rounding
target: atlas-packet-forces-two-s3-covariance-energy
requires:
  - atlas-19243-centrality-forces-s3-distance
  - atlas-19243-relation-forces-s3-distance
  - s3-two-generator-covariance-controls-commutant-distance
---

Let `K=<h_a,h_b> ~= S_3` and let `C_K` be the unitary commutant of its regular
`A_8` action at the current external multiplicity.  Bi-invariance gives

```text
||U rho(h) U^*-rho(h)||_2 = ||U rho(h)-rho(h)U||_2.
```

Therefore `s3-two-generator-covariance-controls-commutant-distance` applies to
the two named atlas covariance defects and yields

```text
dist_2(U,C_K)^2 <= a^2+b^2.                           (1)
```

The established collision-19243 packet estimate gives, for the same `C_K`,

```text
dist_2(U,C_K)
 >= max(0,(sqrt(2)-L_19243 delta)/16).                 (2)
```

Squaring `(2)` and combining with `(1)` proves `(19243-S3-E)`.  If
`delta_n->0`, its right-hand side converges to

```text
(sqrt(2)/16)^2 = 2/256 = 1/128,
```

which is `(19243-S3-FLOOR)`.

If instead the collision word itself has defect `epsilon_q`, substitute the
direct relation wall

```text
dist_2(U,C_K)
 >= max(0,(sqrt(2)-epsilon_q)/8)
```

into `(1)`.  This proves `(19243-REL-S3-E)`, and `epsilon_q(n)->0` gives

```text
(sqrt(2)/8)^2=1/32.
```
