---
rg: 2
id: realized-twists-outer-embedding-proof
kind: route
title: Read the conjugation action of a relative element on sigma(Gamma), then transport it along a compressor using absolute normalization
target: realized-relative-twists-embed-in-outer-twist-group
requires:
  - sofic-groups-kill-rigid-compression-defects
  - rigid-compression-defect-normalization-dichotomy
---

Notation as in the target. Commutators are `[a, b] = a b a^-1 b^-1`.

1. **`N_rel(sigma)` acts on `Gamma_s`.** For `x in N_rel(sigma)` and
   `g in Gamma_s`, `x g x^-1 = [x, g] g` lies in `M_s Gamma_s = Gamma_s`.
   `N_rel(sigma)` is a group (`relative-defect-normalization-dichotomy`), so
   `x^-1` does the same, and `phi_x = Ad(x)|_{Gamma_s}` is an automorphism of
   `Gamma_s`. It satisfies `phi_x(g) g^-1 = [x, g]`, which lies in `M_s`. So
   `phi_x` lies in `Aut_M(Gamma_s)`, and `x -> phi_x` is a homomorphism.
2. **Kernel and inner part.** `phi_x = id` iff `x` commutes with `Gamma_s`, i.e.
   `x in C_s`. And `C_s <= N_rel(sigma)`, since `C_s` centralizes
   `M_s <= Gamma_s`. For `m in M_s`, `phi_m = Ad(m)`. So the preimage of
   `Ad(M_s)` is `M_s . C_s`.
   - `Ad(M_s)` is normal in `Aut_M(Gamma_s)`: `phi . Ad(m) . phi^-1 = Ad(phi(m))`
     and `phi(m) in M_s m = M_s`.
   - Hence `M_s . C_s` is normal in `N_rel(sigma)`, and `Q_s` embeds in
     `Out_M(Gamma_s)`. This proves item 1.
3. **`eps_t` is an endomorphism of `Aut_M(Gamma_s)`.** Let `s = sigma(t)`.
   - For `g in Gamma_s`, `s g s^-1 in sigma(t Gamma t^-1) <= Gamma_s`, so
     `phi(s g s^-1) in M_s . s g s^-1`.
   - Conjugating back, `eps_t(phi)(g) = s^-1 phi(s g s^-1) s` lies in
     `(s^-1 M_s s) g = M_s g`, since `M` is normal in `G`. So `eps_t(phi)` maps
     `Gamma_s` into `Gamma_s` and is trivial modulo `M_s`.
   - It is injective because `phi` is.
   - **Surjective.** Given `g' in Gamma_s`, we need `phi^-1(s g' s^-1)` in
     `s Gamma_s s^-1`. It lies in `M_s . s g' s^-1`, and
     `M_s = s M_s s^-1 <= sigma(t Gamma t^-1)`, so it does.
   - `eps_t(phi psi) = eps_t(phi) eps_t(psi)` by direct substitution, and
     `eps_t(Ad(m)) = Ad(s^-1 m s)` with `s^-1 m s in M_s`.
   So `eps_t` descends to `Out_M(Gamma_s)`.
4. **Compatibility.** For `x in N_rel(sigma)` and `g in Gamma_s`:
   - `s^-1 x s` lies in `N_rel(sigma)`, because
     `[s^-1 x s, g] = s^-1 [x, s g s^-1] s` lies in `s^-1 M_s s = M_s`;
   - `phi_{s^-1 x s}(g) = s^-1 x (s g s^-1) x^-1 s = eps_t(phi_x)(g)`.
5. **Injectivity on `Q_s` (the property (T) input).**
   `sofic-groups-kill-rigid-compression-defects` together with
   `rigid-compression-defect-normalization-dichotomy` gives NORM for every
   homomorphism: `sigma(G)` normalizes `C_s`. If `eps_t(phi_x) in Ad(M_s)`, then
   `s^-1 x s in M_s C_s`, so `x in s M_s C_s s^-1 = M_s C_s`. This proves
   item 2.
6. **Stabilizer form.**
   - If `x in S_U` satisfies `Ad(x) . iota = iota . phi` on `Gamma_s` for some
     `phi in Aut_M(Gamma_s)`, then `x` normalizes `M_s`, because `phi(M_s) = M_s`,
     and `[x, g] = phi(g) g^-1 in M_s`. So `x in N_rel(sigma)`.
   - Conversely, if `x in N_rel(sigma)` realizes `phi_x in phi . Ad(M_s)`, say
     `phi_x = phi . Ad(m)`, then `x m^-1` realizes `phi` exactly.
   This proves item 3.
7. **Normalization.** As in step 6 of `relative-defect-compressor-endomorphism-proof`:
   - `eps_t` is surjective on `Q_s` iff `s N_rel(sigma) s^-1 = N_rel(sigma)`,
     using `s^-1 (M_s C_s) s = M_s C_s` from step 5;
   - compressors generate `G` by infranormality.
   This proves item 4.
8. **Hosts.** If `sigma` is an injective homomorphism of `H`, it identifies
   `Gamma` with `Gamma_s` and `M` with `M_s`. For `z in Z`, `sigma(z) in N_rel(sigma)`
   and `phi_{sigma(z)} = sigma . Ad(z)|_Gamma . sigma^-1`.
   - If `sigma(z) in M_s C_s`, say `sigma(z) = sigma(m) c`, then
     `sigma(m^-1 z)` commutes with `Gamma_s`. By injectivity `m^-1 z in C_H(Gamma)`,
     so `z in M . C_H(Gamma)`.
   - The endomorphisms match by step 4.
   This proves item 5.
