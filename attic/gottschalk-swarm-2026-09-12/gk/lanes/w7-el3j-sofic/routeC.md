---
rg: 2
id: jacobson-one-sided-symbol-preimages-lef-proof
kind: route
title: Truncate at a level, triangularize over F[S], and separate by congruences mod S^k
target: jacobson-one-sided-symbol-preimages-are-lef
requires:
  - jacobson-shift-representation-is-faithful
  - jacobson-elementary-subgroups-are-locally-finite-by-linear
artifacts:
  - research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md
---

**Derivation** (artifact Section 3).

1. **Structure.**
   - `F[z]`, `F[z^(-1)]` and `F` are Euclidean, so `SL_3 = E_3` over each.
   - `π` maps `EL_3(F[S])` isomorphically onto `SL_3(F[z])`, which gives `H_+ = L_3 x| EL_3(F[S])`.
   - `θ(g) = (σ(g)^t)^(-1)`, with `σ` the anti-involution exchanging `S` and `T`, sends `x_ij(a)` to `x_ji(-σ(a))`.
     It commutes with the symbol up to `z -> z^(-1)`, so `θ(H_+) = H_-`.
2. **Truncation.** Split `V^3 = W_N ⊕ U_N` at level `N`.
   - A finitary kernel element supported below level `N` has block form `[[A, 0], [0, 1]]`.
   - `d in EL_3(F[S])` has block form `[[A, 0], [B, d]]`, because `S` raises the level and `U_N = F[S]^3`.
   - With `W_N = F^(3N)`, the block matrices `[[A, 0], [B, D]]`, where `A in GL_(3N)(F)`, `B in M_(3 x 3N)(F[S])` and
     `D in GL_3(F[S])`, multiply as in `GL_(3N+3)(F[S])`.
   - The shift action is faithful (`jacobson-shift-representation-is-faithful`). So every finitely generated subgroup
     of `H_+` embeds in some `GL_(3N+3)(F[S])`.
3. **Separation.** `GL_m(F[S])` is residually finite through `F[S]/(S^k)`. This gives residual finiteness of finitely
   generated subgroups, hence LEF, hence sofic.
4. **Proper cover.** `a = x_12(S)` lies in `H_+ \ H_0` and `b = x_23(T)` in `H_- \ H_0`. So `a b a^(-1) b^(-1)` is
   reduced in the amalgam and not in `H_0`. In `E_F` it equals `x_13(ST) = x_13(1 - Q)`, which lies in `H_0`.
5. **Kernel.** The kernel `L_3` is locally finite (`jacobson-elementary-subgroups-are-locally-finite-by-linear`,
   item 1).
