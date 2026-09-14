---
rg: 2
id: homomorphic-codes-cannot-compress-proof
kind: route
title: Restrict the code to constant configurations and translate by a kernel constant
target: homomorphic-codes-cannot-compress-bernoulli-shifts
requires: []
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Section 5 of the artifact.
1. **Constants to constants.** A constant configuration is fixed by every shift, so its image is
   shift-fixed, hence constant. `tau` therefore restricts to a homomorphism `A -> B` on constants.
2. **Kernel constant.** Since `|B| < |A|`, some `a != 1` is in the kernel, and
   `tau(x c_a) = tau(x) tau(c_a) = tau(x)` while `x c_a != x`.
3. **No conull injectivity set.** Right multiplication by `c_a` preserves the uniform product
   measure. If `S` were conull with `tau` injective on it, `S ∩ S c_a^-1` would be conull, and its
   points give collisions. A translation of the target changes nothing.
