---
rg: 2
id: periodic-higman-spectrum-contains-every-prime-proof
kind: route
title: Certify all remaining prime periods by root bounds and exact resultants
target: periodic-higman-spectrum-contains-every-prime
requires:
  - periodic-higman-algebraic-matrix-certificate
  - periodic-higman-spectrum-is-cofinite
artifacts:
  - research/artifacts/periodic-higman-all-primes-2026-09-05.md
  - experiments/periodic_higman_algebraic_certificate.py
  - experiments/periodic_higman_all_primes_certificate.py
---

The artifact gives a complete computer-assisted proof. The cofinite theorem
handles primes above `B=4000*40^12`. For the remaining odd primes, the
Cayley transform and an exact Sturm calculation isolate the three
unit-circle roots of the certificate polynomial. Rational interval
certificates bound their angles away from every rational with denominator
at most `B`. The other root pair has modulus ratio controlled by `R>4`.
These bounds make the cyclotomic resultant a nonunit for all primes from
200 through `B`; exact integer determinants handle the 45 smaller odd
primes. Reduction at a prime divisor of the resultant supplies the finite
matrix certificate. An explicit `PSL_2(5)` model handles period two.

For any `m>=2`, a certificate for a prime divisor of `m` gives the
asserted finite quotient of `G_m` via a finite semidirect product.
