---
rg: 2
id: rigid-compression-defect-normalization-dichotomy-proof
kind: route
title: Restrict an injective model to the pair, and conversely generate a group from a non-normalized centralizer element
target: rigid-compression-defect-normalization-dichotomy
requires: []
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

Complete derivation, Section 2 of the artifact.

**NORM => DD.**

1. Let `H` be `C`-approximable with rigid pair `Gamma <= G <= H`, and choose
   an injective `rho : H -> U`.
2. Normalization for `rho|G` puts `rho(g) rho(z) rho(g)^-1` in
   `C_U(rho(Gamma))` for every `z in C_H(Gamma)`.
3. So `rho` kills `[g z g^-1, gamma]`, and injectivity kills it in `H`.

**not NORM => not DD.**

1. If `sigma : G -> U` fails to normalize `C = C_U(sigma(Gamma))`, some `g`
   and `z in C` have `sigma(g) z sigma(g)^-1` outside `C`. Otherwise applying
   the inclusion to `g^-1` would give equality.
2. So some `gamma` has `[sigma(g) z sigma(g)^-1, sigma(gamma)] != 1`.
3. The group `<sigma(G), z> <= U` is countable, hence `C`-approximable.
4. It contains the rigid pair `sigma(Gamma) <= sigma(G)`: quotients of
   Kazhdan groups are Kazhdan, and images of compressors are compressors that
   still generate.
5. `z` centralizes `sigma(Gamma)`, so the commutator is a nontrivial rigid
   defect.

**Property (U) for each class.**

- **Sofic, linear sofic, weakly sofic, weak MF:** the ultraproduct form is the
  definition; see Arzhantseva--Paunescu arXiv:1212.6780, Definitions 1.1 and
  4.1.
- **Hyperlinear:** use the inclusion `(+) 1` together with tensor-power
  amplification, as written in the artifact.
