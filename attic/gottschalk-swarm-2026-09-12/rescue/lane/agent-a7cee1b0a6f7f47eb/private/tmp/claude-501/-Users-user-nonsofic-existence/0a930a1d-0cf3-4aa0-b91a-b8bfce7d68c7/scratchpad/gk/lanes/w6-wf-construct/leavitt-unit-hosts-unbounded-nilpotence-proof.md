---
rg: 2
id: leavitt-unit-hosts-unbounded-nilpotence-proof
kind: route
title: Permutation units of p-power order are unipotent in characteristic p, and bounded nilpotence index kills a nonidentity element
target: leavitt-unit-hosts-need-nilpotents-of-unbounded-index
requires:
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**Proof.** Artifact Section 1.

1. **Prefix-code permutations.** For every `n >= 1`, a complete prefix code `w_1, …, w_n` exists, and
   `u_π = Σ_i s_(w_(π(i))) t_(w_i)` is a unit with inverse `u_(π^(-1))`. So `S_n ≤ V ≤ G`, and `G` has elements of every
   order `p^k`.
2. **Unipotence.** In characteristic `p`, the binomial theorem gives `(ρ(x) - 1)^(p^k) = ρ(x)^(p^k) - 1 = 0`. With
   nilpotent index at most `N` and `p^j >= N`, `(ρ(x) - 1)^(p^j) = 0`, which is the same as `ρ(x)^(p^j) = 1`.
3. **Conclusion.** For `k = j + 1`, `y = x^(p^j)` has order `p` and lies in `ker ρ`.
   - For `p = 2`, simplicity of `G` gives `ρ` trivial.
   - For `p = 3`, `y ∉ {±1}` because it has order 3. Under the normal-subgroup input (simplicity of `G_3/{±1}` and
     perfectness), `ker ρ = G_3`, so `ρ(z) = 1 ≠ -1`.
4. **Sharper form.** If `ρ` is nontrivial, or for `p = 3` has `ρ(z) = -1`, no element of order `p` lies in `ker ρ`. So
   `(ρ(x) - 1)^(p^(k-1)) = ρ(x^(p^(k-1))) - 1 ≠ 0`.

**Dead hosts.** A nilpotent `n×n` matrix over a division ring satisfies `x^n = 0`, and a finite-dimensional
algebra embeds in its own left multiplication algebra. Goldie's theorem is used at statement level for Goldie
rings.
