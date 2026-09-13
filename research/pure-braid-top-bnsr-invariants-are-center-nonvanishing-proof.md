---
rg: 2
id: pure-braid-top-bnsr-invariants-are-center-nonvanishing-proof
kind: route
title: The full twist survives, and every other character factors through the split quotient H_n with Euler characteristic (-1)^n (n-2)!
target: pure-braid-top-bnsr-invariants-are-center-nonvanishing
requires:
  - split-quotient-euler-obstruction-to-bnsr-invariants
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md
---

Artifact, Sections 2 and 5.

1. If `chi(Delta^2) != 0` then `chi(Delta) != 0` and `[chi] in Sigma^infinity(P_n)`
   (Zaremsky, arXiv:1507.08597v1, Corollary 3.8). Since `omega_{ij}(Delta) = 1/2`
   for all pairs, `chi(Delta^2) = sum a_{ij}`.
2. If `chi != 0` and `chi(Delta^2) = 0`, write `P_n = H_n x Z` (proof of Theorem
   3.9 there) and `chi = psi o pi` for the split projection `pi: P_n -> H_n`.
3. `H_n` has a finite classifying space of dimension `n - 2` (same proof, citing
   Aramayona–Martínez-Pérez, Corollary 1.3). Its Euler characteristic is
   `(-1)^n (n-2)!`: forgetting the last strand gives `1 -> F_{n-1} -> H_n -> H_{n-1} -> 1`
   (the kernel of `P_n -> P_{n-1}` is `F_{n-1}`, and the full twist maps to the
   full twist), `H_3 = F_2`, and Euler characteristic is multiplicative.
4. `split-quotient-euler-obstruction-to-bnsr-invariants` with `d = n - 2` gives
   `[chi] notin Sigma^{n-2}(P_n)`, hence `notin Sigma^m(P_n)` for `m >= n - 2`.
