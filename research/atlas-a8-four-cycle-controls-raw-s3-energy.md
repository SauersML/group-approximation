---
rg: 2
id: atlas-a8-four-cycle-controls-raw-s3-energy
kind: claim
title: The minimal A8 four-cycle controls the two raw S3 covariance directions with constant twenty-four
artifacts:
  - experiments/atlas_a8_four_cycle_raw_s3.py
  - experiments/atlas-raw-reynolds-gap-audit.json
---

Let `lambda_k` be a regular amplification of `A8=GL_4(F2)`, let `U` be any
unitary, and define

```text
d_t=||[U,lambda_k(t)]||_2,
T={t01,t12,t23,t30}.
```

Let `h_a,h_b` be the two raw-S3 involutions occurring eight and four times in
the compiled raw source word.  In the standard chart coordinates they are
exactly

```text
h_a=t21,
h_b=t12.
```

Then

```text
||[U,lambda_k(h_a)]||_2^2
+||[U,lambda_k(h_b)]||_2^2
 <= 24 sum_(t in T) d_t^2.                              (A8-RAW-24)
```

The constant is dimension- and multiplicity-independent.  It avoids the
full-chart Reynolds/diameter loss in `atlas-a8-four-cycle-commutant-gap`: for
the final raw-S3 contradiction, the four-cycle energy can be sent directly to
the two detector directions.
