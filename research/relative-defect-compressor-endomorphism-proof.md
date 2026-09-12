---
rg: 2
id: relative-defect-compressor-endomorphism-proof
kind: route
title: Normalize the absolute centralizer by the sofic criterion, then read the relative defect on the quotient
target: relative-defect-iff-surjective-compressor-endomorphisms
requires:
  - sofic-groups-kill-rigid-compression-defects
---

Notation as in the target: `H` sofic, `M` normal in `H`, rigid pair
`M <= Gamma <= G <= H`, `Z`, `K = M . C_H(Gamma)`, `Q = Z/K`.

1. **`Z` is a subgroup normalizing `Gamma`.** For `z, z_1, z_2 in Z` and
   `gamma in Gamma`:
   - `[z_1 z_2, gamma] = z_1 [z_2, gamma] z_1^-1 . [z_1, gamma]`, which lies in
     `M` because `M` is normal in `H`;
   - `[z^-1, gamma] = z^-1 [z, gamma]^-1 z`, which lies in `M`;
   - `z gamma z^-1 = [z, gamma] gamma` lies in `M Gamma = Gamma`, and likewise
     for `z^-1`, so `z Gamma z^-1 = Gamma`.
2. **`K` is normal in `Z`.** `M <= Z` because `M` is normal, and
   `C_H(Gamma) <= Z`. `K` is a subgroup because `M` is normal. For `z in Z`,
   `z M z^-1 = M` and `z C_H(Gamma) z^-1 = C_H(z Gamma z^-1) = C_H(Gamma)`.
3. **Compressors shrink `Z`.** Let `t in P_Gamma`, so `t Gamma t^-1 <= Gamma`.
   For `z in Z` and `gamma in Gamma`,
   `[t^-1 z t, gamma] = t^-1 [z, t gamma t^-1] t`, which lies in
   `t^-1 M t = M` since `t gamma t^-1 in Gamma`. So `t^-1 Z t <= Z`.
4. **Compressors fix `K` (the sofic input).** By
   `sofic-groups-kill-rigid-compression-defects`, `[g c g^-1, gamma] = 1` for
   all `c in C_H(Gamma)`, `g in G`, `gamma in Gamma`. So
   `g C_H(Gamma) g^-1 <= C_H(Gamma)` for every `g in G`, with equality by
   applying this to `g^-1`. With `M` normal, `t^-1 K t = K`.
5. **`eps_t` is an injective endomorphism.** It is well-defined by step 4, a
   homomorphism because conjugation is, and injective: `t^-1 z t in K` forces
   `z in t K t^-1 = K`.
6. **Surjectivity versus normalization.**
   - If `t Z t^-1 = Z`, then `eps_t` is surjective.
   - If `eps_t` is surjective, every coset `zK` equals `t^-1 z' t K` for some
     `z' in Z`. So `Z <= (t^-1 Z t) K = (t^-1 Z t)(t^-1 K t) <= t^-1 Z t`, and
     step 3 gives `t^-1 Z t = Z`.
7. **The criterion.** `G` normalizes `Z` iff `[g z g^-1, gamma] in M` for all
   `g, z, gamma`: that is the definition of `Z` applied to `g z g^-1`, with
   equality by `g^-1`. `P_Gamma` generates `G`, so `G` normalizes `Z` iff every
   `t in P_Gamma` satisfies `t Z t^-1 = Z`, iff every `eps_t` is surjective
   by step 6.
8. **Co-Hopfian quotients.** In a co-Hopfian group every injective endomorphism
   is an automorphism, so step 7 gives the criterion. Finite groups are
   co-Hopfian.
9. **Where the hypotheses enter.** Normality of `M` in `H` is used in steps
   1-4. Property (T) of `Gamma` and `G` and soficity of `H` enter only through
   step 4. Property (T) of `M` is never used.
10. **Instances.**
    - Transpose-inverse: `Z = H`, `C_H(SL_3(Z)) = 1`, `K = SL_3(Z)`, so
      `Q = Z/2`.
    - Leavitt cover: `pi(z)` centralizes `pi(Gamma_hat) = EL_alpha(R)` iff
      `[z, Gamma_hat] <= N`, so `Z = pi^-1(C_(R^x)(EL_alpha(R)))`. Non-elementary
      subgroups of hyperbolic groups have finite centralizers, and the cover
      is torsion-free (Belegradek--Osin Corollary 1.2 with a torsion-free
      source, as recorded in `leavitt-cover-finite-quotients-split-over-the-kernel`),
      so `C_G(Gamma_hat) = 1` and `K = N`. The element `z` of Theorem 3(c) of
      `research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md`
      satisfies `u_hat z u_hat^-1 not in Z`, so `eps_u_hat` is not surjective.
