---
rg: 2
id: leavitt-rank-three-support-group-is-virtually-free
kind: claim
title: The units of the rank-three lifts generate a free product of finite groups
distinct_from:
  leavitt-rank-three-unit-lift: that constructs the three units and shows they sum to the generator, an additive statement inside the algebra; this identifies the GROUP they generate, which the additive splitting says nothing about, and it is what makes their group algebra directly finite.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies GL with EL over the Leavitt algebra and proves the whole unit group perfect; this computes one explicit three-generator subgroup and finds it virtually free, hence far from perfect.
  openai-leavitt-unit-nonsofic: that is the nonsoficity of the whole unit group; this exhibits a virtually free — in particular sofic — subgroup of it, which is where the rank-three material had unknowingly been living.
  leavitt-corner-idempotent-unital-surjection: that constructs the order-three unit g and the corner idempotent e; this observes that g is exactly u_3, so the corner also lies in this subgroup, and then computes the subgroup.
artifacts:
  - research/artifacts/leavitt-rank-three-no-inverse-2026-08-18.md
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, and let `u_1,u_2,u_3` and `v_1,v_2,v_3` be
the units of `leavitt-rank-three-unit-lift`, so `t_0 = u_1+u_2+u_3` and
`s_0 = v_1+v_2+v_3`.  Put `K = <u_1,u_2,u_3>` and `K_s = <v_1,v_2,v_3>`.

1. **Structure.**  Both are free products of finite groups:

   ```text
   K  =  K_s  =  (C_2 x C_2) * C_3.
   ```

   Explicitly, with `r = U_3`, `q_0 = U_2U_3 = [[1,t_0],[0,1]]` and
   `q_1 = U_3^(-1)U_1U_3 = [[1,t_1],[0,1]]` in the self-similarity picture,
   `<U_1,U_2,U_3> = <q_0,q_1,r>` with `<q_0,q_1> = C_2 x C_2` and
   `<r> = C_3`; the same computation with `s_i` in place of `t_i` gives `K_s`.

2. **Linearity.**  Both embed in `GL_2(F_2[X])`, by specializing
   `t_0,t_1 |-> X,X^2` (resp. `s_0,s_1 |-> X,X^2`) — legitimate because
   `F_2<t_0,t_1>` and `F_2<s_0,s_1>` are free subalgebras of `R`.  Hence both
   are residually finite by Malcev, and in particular sofic; the free-product
   normal form for the images, read off from Nagao's amalgam decomposition of
   `GL_2(F_2[X])`, is what proves item 1.

3. **The corner lives here too.**  The order-three unit `g = (1+s_0t_1)(1+s_1t_0)`
   of `leavitt-corner-idempotent-unital-surjection` is exactly `u_3`, so the
   corner idempotent `e = [g]+[g^2]` lies in `F_2[K]`.

**Why it matters.**  `openai-leavitt-unit-nonsofic` says `G` is not sofic, and
that is the whole reason this group was chosen to test Kaplansky.  Item 1 says
the explicit material built so far sits inside a *sofic*, indeed virtually
free, subgroup — and `leavitt-rank-three-lift-has-no-one-sided-inverse` is
what that costs.

## Scope

A statement about two explicit three-generator subgroups, nothing more.  It
does not bound the subgroups a future construction may use, and it does not
bear on soficity of `G` itself: a nonsofic group has plenty of virtually free
subgroups, and exhibiting one is not evidence in either direction.
