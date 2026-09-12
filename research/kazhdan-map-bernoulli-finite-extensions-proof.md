---
rg: 2
id: kazhdan-map-bernoulli-finite-extensions-proof
kind: route
title: Enumerate the finite fibres, untwist the permutation cocycle by superrigidity, and use ergodicity
target: kazhdan-map-bernoulli-finite-extensions-are-trivial
requires:
  - popa-bernoulli-cocycle-superrigidity
artifacts:
  - research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md
---

Section 4 of the artifact, Theorem 4.1. Step 0 multiplies the extension by an independent Bernoulli
factor `([0,1], Leb)^G`, so the imported theorem is consumed only for the s-malleable diffuse-base
Bernoulli action. Only finite targets `Sym(n)` are used. The absence of finite quotients kills the
resulting homomorphism.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 12 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Trust surface: whether Popa Theorem 0.1 covers atomic bases.

**Scope correction 2026-09-12 (gk-p-inf-kazhdan).** Step 0 of Theorem 4.1 removes that trust
surface. `Z x Y` is an ergodic finite extension of `X x Y ~= ([0,1], Leb)^G` with the same
multiplicity, so no atomic-base form of the import is needed. Step 0 was added after the verification
above and has not been re-verified.
