---
rg: 2
id: topologically-free-matricial-crossed-el-simple-kazhdan-lef-proof
kind: route
title: Simplicity by the topologically free tower criterion, property (T) by Ershov–Jaikin-Zapirain, LEF from the kernel of the ultraproduct map
target: topologically-free-matricial-crossed-el-simple-kazhdan-lef
requires:
  - binary-el-simple-iff-minimal-topologically-free
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/sk-simpler-unify-proposal-2026-09-13.md
---

Notation: `G = EL_n(R)`, `n ≥ 3`, `R = LC(Z,F_2) ⋊ L`, and `φ: R → ∏_ω M_{N_k}(F_2)` a unital ring homomorphism.

1. **Finite generation.** Take a finite generating set `S` of `R` with `1 ∈ S`. By `e_ij(r+s) = e_ij(r)e_ij(s)` and `[e_ik(r),e_kj(s)] = e_ij(rs)` for distinct `i,j,k`, the matrices `e_ij(s)`, `s ∈ S`, generate `G`.
2. **Infinite.** `e_12(LC(Z,F_2))` is infinite, because `Z` is a Cantor set.
3. **Property (T).** `R` is finitely generated, so `elementary-groups-over-fg-rings-have-property-t` applies.
4. **Simplicity, with trivial centre.** The forward direction of `binary-el-simple-iff-minimal-topologically-free` applies, since the action is minimal and topologically free. A self-contained elementary proof is §1 of the artifact:
   - small clopen sets are dense, by topological freeness;
   - a nontrivial `g ∈ N` fails to commute with some `h = e_ij(e_V)` with `V` small;
   - `k = [g,h]` lies in one copy of `GL_d(F_2)`, `d = n|B_w|`, spanned by the matrix units `ε_ab = e_{aV}u_{ab^{-1}}`, `a,b ∈ B_w`;
   - that group is simple, so `N` contains it;
   - the level ideal contains `1`, because finitely many translates `ℓV` cover `Z`.
5. **LEF.**
   - `φ` is unital, so it induces a group homomorphism `G → ∏_ω GL_{nN_k}(F_2)`. An element of the matrix ultraproduct is invertible exactly when ω-almost all components are.
   - The kernel is a normal subgroup that misses `e_12(1)`, whose image is `I + E_12 ≠ I`. By step 4 it is trivial, so `G` embeds in an algebraic ultraproduct of finite groups.
   - `R` is countable, since `Z` is second countable and `L` is countable. So `G` is countable.
   - A countable subgroup of an algebraic ultraproduct of finite groups is LEF. For finite `F ⊆ G`, the finitely many distinctness and product relations among elements of `F` hold in ω-almost every coordinate, and one such coordinate is an injective partial homomorphism into a finite group.

**Firewall.** Nothing here uses `a ↦ diag(a,a^{-1},1)` as a homomorphism (`whitehead-diagonal-map-is-not-multiplicative`).
