---
rg: 2
id: leavitt-unit-hosts-need-nilpotents-of-unbounded-index-proof
kind: route
title: Permutation units of p-power order are unipotent in characteristic p, and bounded nilpotence index kills an element of order p
target: leavitt-unit-hosts-need-nilpotents-of-unbounded-index
requires:
  - binary-leavitt-unit-group-is-simple
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**Proof.** Artifact Sections 1 and 3.

1. **Prefix-code permutations.** For `n >= 2`, `u_π = Σ_i s_(w_(π(i))) t_(w_i)` over a complete prefix code
   `w_1, …, w_n` embeds `S_n` in `V ≤ G`. So `G` has elements of every order `p^k`.
2. **Unipotence.** In characteristic `p`, `(ρ(x) - 1)^(p^j) = ρ(x)^(p^j) - 1`. With nilpotence index at most `N`
   and `p^j >= N`, this gives `ρ(x)^(p^j) = 1`.
3. **Kernel.** For `x` of order `p^(j+1)`, `y = x^(p^j)` has order `p` and lies in `ker ρ`.
   - For `p = 2`, `G` is simple, so `ρ` is trivial.
   - For `p = 3`, every normal subgroup lies in `{±1}` or equals `G_3`: combine simplicity of `G_3/{±1}` with
     perfectness, `G_3 = [M{±1}, M{±1}] = [M, M]`. Since `y ∉ {±1}`, `ker ρ = G_3` and `ρ(z) = 1 ≠ -1`.
4. **Sharper form.** The same kernel argument shows `ker ρ` has no element of order `p`. So
   `(ρ(x) - 1)^(p^(k-1)) = ρ(x^(p^(k-1))) - 1 ≠ 0`.
5. **Corollary A.2.**
   - Let `𝔫 = {a : rk(a) = 0}`, an ideal. On `F_2[G]/𝔫`, `ρ` is nontrivial unless `rk = rk_ε`; for `p = 3`,
     `rk(1 + [z]) = 0` gives `ρ(z) = -1`.
   - The Frobenius inequality `rk(XY) + rk(YZ) <= rk(Y) + rk(XYZ)` comes from `diag(Y, XYZ) ~ [[Y, YZ], [-XY, 0]]`
     and the triangular axiom.
   - It makes the differences `d_j = rk(a^j) - rk(a^(j+1))` non-increasing.
   - So `d_0, …, d_(m-1)` are positive and sum to 1, where `m > p^(k-1)` is the first index with `rk(a^m) = 0`.

**Dead hosts.** A nilpotent `n×n` matrix over a division ring satisfies `x^n = 0`, and a finite-dimensional
algebra acts faithfully on itself by left multiplication. Goldie's theorem is used at statement level.
