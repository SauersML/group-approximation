---
rg: 2
id: zd-full-group-lef-relator-shift-criterion-proof
kind: route
title: Relator-shift periodic points give finite permutation groups with exactly the short relators
target: zd-subshift-full-group-lef-via-periodic-relator-shifts
requires: []
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
---

## Why sufficient

Notation as in the target; sup norms throughout.

1. **`Z_n` is an SFT containing `Omega`.**
   - For `w = s_k ... s_1`, `ĉ_w(z) = Σ_i ĉ_{s_i}(ŝ_{i-1} ... ŝ_1 z)` depends only on `z|B((k-1)R + R')`. Each condition is local, and there are finitely many words.
   - On `x ∈ Omega` every `ĉ_s` equals `c_s`, so `ĉ_w(x) = c_w(x)`.
   - If `w` is trivial in `Gamma`, then `sigma^{c_w(x)} x = x`, and freeness gives `c_w(x) = 0`.
2. **Permutations.**
   - Let `O` be the finite shift orbit of `y_n`. Each `ŝ` maps `O` into `O`, because `ŝ(z)` is a translate of `z`.
   - The word `s^{-1} s` is trivial and has length 2, so `ĉ_{s^{-1}s} = 0` on `O`. So the extension of `s^{-1}`, composed with `ŝ`, is the identity on `O`.
   - Hence `ŝ|_O` is a bijection of the finite set `O`. Let `pi : F(S) -> G_n = <ŝ|_O : s ∈ S> ≤ Sym(O)`.
3. **Short trivial words.** If `|w| <= 2n` and `w = 1` in `Gamma`, then `ĉ_w = 0` on `O ⊆ Z_n`. So `ŵ = id` on `O` and `pi(w) = 1`.
4. **Short nontrivial words.**
   - Let `|w| <= 2n` with `w ≠ 1` in `Gamma`. Pick `x ∈ Omega` with `w(x) ≠ x`. Then `u = c_w(x) ≠ 0`, and `|u| <= 2nR`.
   - By (H1), some `z ∈ O` has `z|B(2nR') = x|B(2nR')`.
   - By induction on `i`, after `i` letters the images of `z` and `x` agree on `B(2nR' - iR)`. For `i <= 2n - 1` this contains `B(R')`, so each letter reads a legal window and moves both configurations by the same vector.
   - So `ĉ_w(z) = u`. By (H2), `u ∉ L_n`, so `ŵ(z) = sigma^u z ≠ z` and `pi(w) ≠ 1`.
5. **LEF.** By steps 3 and 4, `ker pi` and `ker(F(S) -> Gamma)` contain the same words of length `<= 2n`. So the balls of radius `n` of the Cayley graphs of `(G_n, pi(S))` and `(Gamma, S)` agree. The finite marked groups `(G_n, pi(S))` converge to `(Gamma, S)`, and `Gamma` is LEF.
6. **Minimal case.**
   - Uniform recurrence gives `rho` such that every legal patch of radius `rho` contains every legal pattern of radius `2nR'`.
   - Suppose that for every `rho` some legal pattern of radius `rho` had a period `u` with `0 < |u| <= 2nR`. There are finitely many such `u`, so pass to a subsequence with constant `u`. A limit point is then a point of `Omega` fixed by `sigma^u`, which contradicts freeness.
   - So one legal patch of large enough radius in `y_n` gives both (H1) and (H2).
