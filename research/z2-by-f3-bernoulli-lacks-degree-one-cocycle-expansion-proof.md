---
rg: 2
id: z2-by-f3-bernoulli-lacks-degree-one-cocycle-expansion-proof
kind: route
title: Z^2 x| F_3 is an HNN extension of Z^2 x| F_2 over Z^2 with an incompatible character, and Popa applies
target: z2-by-f3-bernoulli-lacks-degree-one-cocycle-expansion
requires:
  - amenable-hnn-seams-break-bernoulli-degree-one-expansion
  - popa-bernoulli-cocycle-superrigidity
  - elementary-linear-semidir-pair-relative-t
artifacts:
  - research/artifacts/bernoulli-degree-one-expansion-amenable-seam-2026-09-13.md
---

Artifact Section 6.

1. **HNN structure.** `Gamma` is the HNN extension of `A_0 = Z^2 x| F(t_1, t_2)` over `C = Z^2`, with
   `theta = phi(t_3)`. `A_0` contains `F_2`, so it is nonamenable.
2. **Incompatible character.** `chi(e_1) = 1`, `chi(e_2) = chi(t_i) = 0` respects the `A_0` relators:
   `chi(2e_1 + e_2) = chi(e_2)` and `chi(e_1 + 2e_2) = chi(e_1)`. Also
   `chi(theta e_2) - chi(e_2) = chi(e_1 + e_2) - chi(e_2) = 1`.
3. **Relative (T).**
   - `elementary-linear-semidir-pair-relative-t` with `R = Z` gives relative (T) for `(Z^2 x| SL_2(Z), Z^2)`.
   - The Sanov subgroup `<phi(t_1), phi(t_2)>` is free of index 12 (recalled). So `A_0` is a finite-index subgroup
     containing `Z^2`.
   - **Lemma FI.** If `N` is normal in `G`, `(G, N)` has relative (T) and `N <= G_1` with `G_1` of finite index, then
     `(G_1, N)` has relative (T). Induce the representation, find an `N`-invariant `f`, and evaluate it at a coset
     representative `x` with `f(x) != 0`; normality turns `f(x)` into an `N`-invariant vector.
   - **Lemma UP.** Relative (T) passes from `(A_0, Z^2)` to `(Gamma, Z^2)` by restricting representations.
4. **Popa.** `Z^2` is an infinite normal subgroup with relative (T), and the Bernoulli shift is mixing on it. So
   `popa-bernoulli-cocycle-superrigidity` makes every Z/2-cocycle cohomologous to a homomorphism.
5. **Conclusion.** `amenable-hnn-seams-break-bernoulli-degree-one-expansion` applies with `|S_0| = 4`.
