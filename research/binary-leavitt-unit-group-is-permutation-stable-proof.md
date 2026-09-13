---
rg: 2
id: binary-leavitt-unit-group-is-permutation-stable-proof
kind: route
title: Nonsoficity forces the regular weight of every fixed-point character of the Leavitt unit group to vanish
target: binary-leavitt-unit-group-is-permutation-stable
requires:
  - binary-leavitt-full-character-simplex
  - openai-leavitt-unit-nonsofic
---

Let `H = L_(F_2)(1,2)^x` and let `phi_n : H -> Sym(k_n)` be an almost-homomorphism. Fix a nonprincipal
ultrafilter `omega` and put `chi(g) = lim_omega |Fix phi_n(g)| / k_n`.

1. **`chi` is a character.** The verification is word for word that of
   `research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md`, Section 2, (a)--(c).
   - `phi_n(e)^2` is close to `phi_n(e)`, so `phi_n(e)` is close to `id` and `chi(e) = 1`.
   - Bi-invariance of `d` makes `chi` a class function.
   - For permutations `sigma_i`, the identity
     `sum c_i conj(c_j) |Fix(sigma_j^-1 sigma_i)| = sum_(x,y) |sum_i c_i [sigma_i x = y]|^2 >= 0`,
     together with `|Fix phi_n(g_j^-1 g_i)| - |Fix(phi_n(g_j)^-1 phi_n(g_i))| = o(k_n)`, gives positive
     definiteness.
2. **Simplex.** By `binary-leavitt-full-character-simplex`, `chi = a 1 + (1-a) delta_1` with
   `a in [0,1]`. So every `g != e` has fixed-point proportion `a` along `omega`.
3. **Amplification.** Suppose `a < 1`. For `m >= 1`, let `phi_n^(m)` act coordinatewise on `[k_n]^m`.
   - The defect on each pair grows at most by a factor `m`, by a union bound.
   - The fixed-point proportion of every `g != e` tends to `a^m` along `omega`.

   Given a finite `E ⊆ H` and `epsilon > 0`, choose `m` with `a^m < epsilon/2` and then `n` in an
   `omega`-large set. The result is a sofic approximation on `E`, so `H` is sofic. That contradicts
   `openai-leavitt-unit-nonsofic`.
4. **Conclusion.** So `a = 1` along every nonprincipal ultrafilter.
   - This means `lim_omega d(phi_n(g), id) = 0` for every `omega` and every `g`, hence
     `d(phi_n(g), id) -> 0`.
   - The trivial homomorphisms `psi_n = id` are therefore pointwise close to `phi_n`: `H` is stable.
   - Stability implies the weak and local variants (Bradford, Remark 1.5).
   - It also implies flexible stability, where one may pass to supersets `Y_n ⊇ [k_n]` with
     `|Y_n \ [k_n]| = o(k_n)`, since `psi_n` is already a genuine action on `[k_n]`.

**Non-residual-finiteness.** `V <= H` by `leavitt-cylinder-swaps-generate-thompson-in-el`. `V` is
infinite and simple (`thompson-v-finitely-presented-infinite-simple`), so it has no nontrivial finite
quotient. Residual finiteness passes to subgroups, so `H` is not residually finite.
