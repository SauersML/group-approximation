---
rg: 2
id: thompson-f-spatial-permutation-models-almost-commute-proof
kind: route
title: Counting measures pushed to the interval are almost x_0-invariant, so the wandering window [1/4,3/4] gets mass at most sqrt(6δ)
target: thompson-f-spatial-permutation-models-almost-commute
requires: []
artifacts:
  - research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md
---

The full proof is in the artifact, §§1–2. Steps:

1. **Support.** `c = x_0 x_1 x_0^-1 x_1^-1` fixes `[0,1/4] ∪ [3/4,1]` pointwise.
   - For `s ≤ 1/4`, the chain is `s ↦ s ↦ 2s ↦ 2s ↦ s`.
   - For `s ≥ 3/4`, it is `s ↦ (s+1)/2 ↦ (s+3)/4 ↦ (s+1)/2 ↦ s`.
2. **Word paths.** Call `s` bad for `A` when `π(As) ≠ x_0 π(s)`, and likewise for `B`.
   - `A^-1` is bad at `t` only if `A` is bad at `A^-1 t`, so each letter has at most `δ|S|` bad points.
   - Suffixes of `w(A,B)` are injective, so at most `|w| δ |S|` points meet a bad step.
   - Every other `s` has `π(w(A,B)s) = w(x_0,x_1)π(s)`. When `w(x_0,x_1) = 1`, injectivity of `π`
     gives `w(A,B)s = s`.
3. **Wandering window.** Let `ν_i` be the image of the uniform probability on `S` under `p_i ∘ π`.
   - Step 2 with `w = a^j` gives `ν_i(x_0^j K) ≥ ν_i(K) - jδ` for `K = [1/4,3/4]`.
   - The sets `x_0^(3j)K` are pairwise disjoint, since `x_0^3(3/4) = 1/8 < 1/4`. So
     `ν_i(K) ≤ 1/N + 3δ(N-1)/2` for every `N ≥ 1`.
   - `N = ⌈sqrt(2/(3δ))⌉` gives `ν_i(K) ≤ sqrt(6δ)`.
4. **Commutator.** Suppose `ABA^-1B^-1` moves `s`. Then either its 4-step path has a bad step, or
   `c` moves `π(s)`, which forces some `p_i π(s)` into `K`.
   - This gives `d(AB,BA) ≤ 4δ + k sqrt(6δ)`.
   - Here `d(AB,BA)` equals the fraction moved by `ABA^-1B^-1`, since `ABu ≠ BAu` iff
     `ABA^-1B^-1` moves `BAu`.
5. **Instances.**
   - Intervals: `c[x,y] = [cx, cy]`.
   - Configurations: `c` fixes a configuration once it fixes each point.
   - Cantor set: a word with binary value outside `K` lies in the cylinder `00` or `11`, where `c`
     acts as the identity.
6. **Relators are identity maps.**
   - Generators break only at `D_3` and map `D_s` into `D_(s+1)` for `s ≥ 3`, and so do their inverses.
   - So a word of length `ℓ` breaks only at `D_(ℓ+2)`.
   - `R_1` and `R_2`, of lengths 10 and 14, fix all of `D_17` (exact check in the artifact's log).
