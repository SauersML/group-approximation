---
rg: 2
id: leavitt-packet-linear-sofic-kaplansky-proof
kind: route
title: Identify the packet with R^x, then apply stable finiteness of linear sofic group algebras
target: leavitt-packet-linear-sofic-kills-kaplansky-target
requires:
  - openai-nine-leaf-leavitt-configuration
  - leavitt-gl-equals-el-and-perfect-unit-group
  - linear-sofic-group-algebra-is-stably-finite
---

## Why sufficient

1. **The packet is `R^x`.**
   - [[openai-nine-leaf-leavitt-configuration]] gives `G = <Gamma, u, v> = EL_D(R)`,
     where `EL_D(R)` is `EL_9(R)` transported into `R^x` by the prefix-code
     isomorphism `M_9(R) =~ R` of the complete nine-leaf code `D`.
   - [[leavitt-gl-equals-el-and-perfect-unit-group]] gives `GL_m(R) = EL_m(R)`
     for `m >= 2`, so `EL_D(R) = GL_D(R)`.
   - `GL_D(R)` is the image of `GL_9(R)` under that isomorphism, which is all
     of `R^x`. The same identification is Kun--Thom arXiv:2608.06222,
     Corollary 4.4, as recorded in the configuration node.
2. **The hinge is a whole-group question.** Linear soficity over a field is
   inherited by subgroups, and by step 1 the packet is the whole group. So
   `F_2`-linear soficity of the packet is `F_2`-linear soficity of `R^x`.
3. **Stable finiteness.** If `R^x` is `F_2`-linear sofic, then
   [[linear-sofic-group-algebra-is-stably-finite]] makes `F_2[R^x]` stably
   finite.
   - For a field `K` containing `F_2`, the rank of a matrix over `F_2` equals
     its rank over `K`.
   - So `prod_omega GL_n(F_2) / d_rank` embeds isometrically in
     `prod_omega GL_n(K) / d_rank`, and `R^x` is `K`-linear sofic.
   - The same claim then makes `K[R^x]` stably finite.
   - Hence no `alpha beta = 1 != beta alpha` exists over any field of
     characteristic two, and
     [[leavitt-unit-group-algebra-not-directly-finite]] fails.
4. **Contrapositive.** A strict one-sided inverse pair over some `K` of
   characteristic two makes `R^x` not `K`-linear sofic, so by step 3 not
   `F_2`-linear sofic, so by step 2 the packet is not `F_2`-linear sofic.
