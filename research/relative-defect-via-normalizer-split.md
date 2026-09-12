---
rg: 2
id: relative-defect-via-normalizer-split
kind: route
title: Absorb the relative element into the Kazhdan kernel, then apply Kun--Thom normalization
target: sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels
requires:
  - relative-element-splits-into-m-times-centralizer
  - kun-thom-sofic-centralizer-normalization
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

Let `H` be countable sofic, `M` a normal Kazhdan subgroup, and
`M <= Gamma <= G <= H` a rigid pair. Fix an injective sofic representation
`sigma : H -> S_U` with vanishing trace off the identity (`H` sofic, so one
exists: amplify a sofic approximation, then restrict). Take `z in H` with
`[z, Gamma] <= M`, and `g in G`, `gamma in Gamma`.

1. **Split `z`.** By `relative-element-splits-into-m-times-centralizer`,
   `sigma(z) = sigma(m_0) c` with `m_0` in the image of `M` and
   `c in C_{S_U}(sigma(Gamma))`.

2. **Transport by `g`.** `sigma(g z g^-1) = sigma(g) sigma(m_0) sigma(g)^-1 . sigma(g) c sigma(g)^-1`.
   - `sigma(g) sigma(m_0) sigma(g)^-1 = sigma(g m_0 g^-1) in sigma(M)`, since
     `M` is normal in `H` and `g in H`.
   - `sigma(g) c sigma(g)^-1 in C_{S_U}(sigma(Gamma))` by
     `kun-thom-sofic-centralizer-normalization`: `sigma(G)` normalizes
     `C(sigma(Gamma))`.
   So `sigma(g z g^-1) = sigma(m_1) c_1` with `m_1 in sigma(M)`,
   `c_1 in C(sigma(Gamma))`.

3. **Commute with `gamma`.** Because `c_1` centralizes `sigma(gamma)`,

   ```text
   sigma(g z g^-1) sigma(gamma) sigma(g z g^-1)^-1
       = sigma(m_1) c_1 sigma(gamma) c_1^-1 sigma(m_1)^-1
       = sigma(m_1) sigma(gamma) sigma(m_1)^-1 .
   ```

   Hence `[sigma(g z g^-1), sigma(gamma)] = sigma(m_1) sigma(gamma) sigma(m_1)^-1 sigma(gamma)^-1`.

4. **Land in `M`.** `M` is normal in `H` and `M <= Gamma`, so
   `gamma m_1^-1 gamma^-1 in sigma(M)` and the displayed commutator equals
   `sigma(m_1 . gamma m_1^-1 gamma^-1) in sigma(M)`.

5. **Injectivity.** `sigma` is injective on `H`, so
   `[g z g^-1, gamma] in M`. This is exactly
   `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`. ∎

**How this differs from `relative-rigid-defect-from-kazhdan-quotient-permanence`.**
That route needs `H/M` to be sofic, an open premise at least as strong as the
target. This route never forms a sofic model of `H/M`: it uses only one sofic
representation of `H`, the Kun--Thom normalization theorem, and the splitting
of `sigma(z)`. All the remaining difficulty is concentrated in the single open
premise `relative-element-splits-into-m-times-centralizer`.
