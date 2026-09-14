---
rg: 2
id: ternary-anti-central-failures-transfer-into-kernel-corners-proof
kind: route
title: Amplify onto level-two cylinders and multiply by the commuting Klein idempotent
target: ternary-anti-central-failures-transfer-into-kernel-corners
requires: [ternary-anti-central-kernel-has-klein-idempotents]
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Section 4 of the artifact.
* `delta4` is a homomorphism, since `T[gamma] S[gamma'] = delta_(gamma gamma')` and
  `sum q_gamma = 1`. It is injective, since `T[00] delta4(g) S[00] = g`.
* Constants `h = sum lambda(gamma) q_gamma` commute with `delta4(g)`, so `E` commutes with
  `delta4_*(S)` and `mu` is multiplicative.
* `delta4(g) h = delta4(g') h'` forces `delta4(g^-1 g')` to be a scalar lying in `H`, hence `1`.
  So the products are distinct group elements and `mu` is injective.
* `pi(E) = 0` gives `pi mu = 0`.
* The pair `((eps_- - q) + mu(a), (eps_- - q) + mu(c))` has vanishing cross terms, because `mu`
  lands in `q S_- q`.
