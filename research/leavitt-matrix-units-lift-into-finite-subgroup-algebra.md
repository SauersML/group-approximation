---
rg: 2
id: leavitt-matrix-units-lift-into-finite-subgroup-algebra
kind: claim
title: The Leavitt matrix units s_i t_j lift to an explicit matrix-unit system in the group algebra of a constant S_3
distinct_from:
  leavitt-matrix-amplification-in-unit-group-algebra: that uses the block e F_2[H] e ~= M_2(F_2) abstractly to place M_2 of the group algebra inside eSe; this names the four lifted matrix units with their supports and records their evaluations s_i t_j.
  augmentation-blocks-unital-leavitt-family: that forbids a unital binary Leavitt family in the group algebra; these units carry no lift of s_0 or t_0 and sum to the proper idempotent e, not to 1.
artifacts:
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

Let `H = <u, v>` with `u = 1 + s_0 t_1`, `v = 1 + s_1 t_0`, `g = uv`, `w = uvu`, a
constant copy of `S_3` in `L_(F_2)(1,2)^x`, and `e = [g] + [g^2]`. In `F_2[H]`:

    f_11 = [1] + [u] + [v] + [g],     f_22 = [1] + [u] + [v] + [g^2],
    f_12 = [g] + [g^2] + [v] + [w],   f_21 = [g] + [g^2] + [w] + [u].

These satisfy `f_ij f_kl = delta_jk f_il`, `f_11 + f_22 = e` (a central idempotent of
`F_2[H]`) and `pi(f_ij) = s_i t_j`. Together with the scalar copy `delta`, they realize
`M_2` of the group algebra inside `eSe`, compatibly with `Theta_2`:
`pi(delta(x) f_ij) = s_i pi(x) t_j`.

Proof: Lemma 5 of the artifact.
