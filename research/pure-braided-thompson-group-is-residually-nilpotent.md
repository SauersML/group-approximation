---
rg: 2
id: pure-braided-thompson-group-is-residually-nilpotent
kind: claim
title: The pure braided kernel P_br of bV -> V is residually nilpotent, compatibly with its pure braid stages
distinct_from:
  residually-nilpotent-implies-lef: that claim is a general implication from residual nilpotence to LEF; this claim proves residual nilpotence for one specific group and records how its lower central series meets the finite stages
---

Let `P_br = ker(V_br -> V)`. It is the directed union, over binary trees `T`, of the
copies `PB_T = {(T, p, T) : p in PB_n(T)}` of the pure braid groups under cloning.
For every tree `T` and every `c >= 1`:

- `gamma_c(P_br) ∩ PB_T = gamma_c(PB_T)`, and
- `∩_c gamma_c(P_br) = 1`.

Consequently each `gamma_c(PB_T)/gamma_{c+1}(PB_T)` embeds in
`gamma_c(P_br)/gamma_{c+1}(P_br)`, and the latter is the directed union of these images.
