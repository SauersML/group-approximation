---
rg: 2
id: klein-expectation-splits-in-balanced-algebra-proof
kind: route
title: Square the one-level splitting and average signs and prefix permutations at level two
target: klein-expectation-splits-in-balanced-algebra
requires:
  - ternary-adjoint-image-is-balanced
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
---

- `Psi delta = 1 (x) 1`, so `rho(e_K) delta^2 = delta (Psi delta) delta = delta^2` and `Psi^2 delta^2 = 1 (x) 1`.
- Both multiplications of `delta^2` and `Psi^2` equal `4 = 1`, so the balanced invariant accepts both.
- For `K_4`: the sign average gives `sum_alpha e_(alpha alpha) (x) e_(alpha alpha)`, and the regular
  prefix average then gives `sum_(alpha,beta) e_(beta alpha) (x) e_(alpha beta) = delta^2 Psi^2`.

Propositions 5 and 6 of the artifact.
