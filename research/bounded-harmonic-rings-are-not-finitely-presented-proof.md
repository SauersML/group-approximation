---
rg: 2
id: bounded-harmonic-rings-are-not-finitely-presented-proof
kind: route
title: Truncate the harmonic function at level k; finitely many relations survive while every large prime stops being invertible
target: bounded-harmonic-rings-are-not-finitely-presented
requires:
  - harmonic-elimination-puts-q-in-odometer-crossed-products
artifacts:
  - research/artifacts/gq-steinberg-q-harmonic-truncation.md
---

The proof is written in the target node. The only input is `Q ⊆ R`, which comes from the harmonic elimination
identity. Otherwise it uses only the crossed-product basis `{u_γ}` and freeness of the odometer action.

- The truncation `f_k` agrees with `f` below level `k` and on the base orbit.
- By the realized-levels argument, `f_k` satisfies any finite set of polynomial identities of `R` once `k` is
  large.
- `f_k` takes values in `Z[1/(k+1)!]`.
- A finite presentation of `R`, of a ring mapping to `R`, or of `E_N(R)` would therefore map to a ring in which
  large primes are not invertible, which contradicts `Q ⊆ R`.
