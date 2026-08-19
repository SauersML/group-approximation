---
rg: 2
id: atlas-packet-energy-controls-s3-covariance-proof
kind: route
title: Project the relative chart unitary to the right-regular commutant
target: atlas-packet-energy-controls-s3-covariance
requires:
  - atlas-packet-routing-commutant-gap
---

Let `C=lambda_k(A8)'` and let `Y` be the Hilbert--Schmidt orthogonal projection
of `U` onto `C`.  For either `h in {h_a,h_b}`, every element of `C` commutes
with `lambda_k(h)`, so

```text
||U lambda_k(h)-lambda_k(h) U||_2
 = ||(U-Y)lambda_k(h)-lambda_k(h)(U-Y)||_2
 <= 2 ||U-Y||_2.                                      (1)
```

Conjugating on the right by `U^*` shows that the left side of `(1)` is exactly
the corresponding covariance defect.  Hence

```text
a(U)^2+b(U)^2 <= 8 dist_2(U,C)^2.                     (2)
```

Apply `atlas-packet-routing-commutant-gap` to `X=U`:

```text
dist_2(U,C)^2 <= (28363/10080) E_packet(U).
```

Combining with `(2)` gives

```text
a(U)^2+b(U)^2
 <= 8*(28363/10080) E_packet(U)
 = (28363/1260) E_packet(U),
```

uniformly in `k`.
