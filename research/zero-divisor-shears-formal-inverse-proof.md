---
rg: 2
id: zero-divisor-shears-formal-inverse-proof
kind: route
title: The control projection annihilates the target embedding, so the shear telescopes formally
target: zero-divisor-shears-are-formal-automorphisms
requires: []
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

Artifact, Section 3, Theorem 5.
1. **Exact linear composition.** For `u, v` over `k[G]`, the polynomial map `L_u(L_v X)` at cell `h` is
   `sum_(m,n) u_m v_n X_(hmn)`, which is `L_(uv) X`.
2. **Controls are unchanged.** `L_B(X + L_A W) = L_B X + L_(BA) W = L_B X` for any polynomial vector `W`.
3. **Telescoping.** `T'(T(X)) = T(X) − L_A Gamma~(L_B T(X)) = X + L_A Gamma~(L_B X) − L_A Gamma~(L_B X)
   = X`, and `T(T'(X)) = X` in the same way.
