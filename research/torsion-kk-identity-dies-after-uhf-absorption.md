---
rg: 2
id: torsion-kk-identity-dies-after-uhf-absorption
kind: claim
title: A torsion KK-identity class vanishes after absorbing a UHF algebra that inverts its order
distinct_from:
  coprime-uhf-stabilizations-detect-uct: that splits the UCT of one algebra into two UHF-localized halves; this computes one of those halves outright when the identity class is torsion.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (derivation, this repository).**  Let `A` be a separable
C\*-algebra and `n ≥ 1` with `n · [id_A] = 0` in `KK(A, A)`.  Let `P` be a set of
primes containing every prime divisor of `n`.  Then `A ⊗ M_(P^∞)` is
KK-contractible, and in particular satisfies the UCT.

So for separable nuclear `A` with torsion identity class of order `n`, the
UCT-support filter of `coprime-uhf-stabilizations-detect-uct` contains the set of
prime divisors of `n`.  If `A` fails the UCT and `n = p^a` is a prime power, then
`{p}` is the unique singleton in that filter: `A ⊗ M_(q^∞)` fails the UCT for
every prime `q ≠ p`.

Proof: `torsion-kk-identity-uhf-proof`.
