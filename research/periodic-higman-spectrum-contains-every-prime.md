---
rg: 2
id: periodic-higman-spectrum-contains-every-prime
kind: claim
title: Every prime belongs to the periodic-Higman spectrum
artifacts:
  - research/artifacts/periodic-higman-all-primes-2026-09-05.md
  - experiments/periodic_higman_all_primes_certificate.py
distinct_from:
  periodic-higman-spectrum-contains-three: that supplies only one prime period; this covers every prime and refutes the missing-prime premise for every filling threshold.
  periodic-higman-spectrum-is-cofinite: that covers all sufficiently large integers but leaves finitely many primes undecided; this covers every prime, including the small ones, and does not assert membership of every composite.
---

Every prime belongs to the spectrum `Sigma` defined in
`periodic-higman-period-spectrum-criterion`.

Consequently every filling `G_m` with `m>=2` has a finite quotient in
which all four base generators are nonidentity. No integer `m>=2` has
the property that no member of `Sigma` divides `m`.

The claim `periodic-higman-large-prime-period-gap` is therefore false,
regardless of the filling threshold. This does not establish residual
finiteness of any `G_m` or settle Gromov's question.
