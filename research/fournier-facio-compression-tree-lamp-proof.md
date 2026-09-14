---
rg: 2
id: fournier-facio-compression-tree-lamp-proof
kind: route
title: Push the commuting triple S x P_1 x P_2 through both stable letters and use centerless rigidity
target: fournier-facio-compression-tree-lamp-group
requires:
  - fournier-facio-torsion-free-skeleton
---

The skeleton proof records `P >= P_1 x P_2 x S` with `u_i P u_i^-1 = P_i` in
the double HNN extension `E`, and `pi:E -> G` with `Gamma = pi(P)`,
`t_i = pi(u_i)`, and `pi|_S` injective.

**(TL1).**  `alpha_i(Gamma) = pi(u_i P u_i^-1) = pi(P_i)`, and `P_1`, `P_2`,
`S` pairwise commute in `P`.

**(TL2), (TL5).**  `S_i = t_i pi(S) t_i^-1 <= t_i Gamma t_i^-1 <= Gamma`.  By
induction, `S_(iw) = t_i S_w t_i^-1 <= alpha_i(Gamma) <= Gamma`.

**(TL3).**  Let `c` be the longest common prefix of `w` and `v`.  If `w = c i w'`
and `v = c j v'` with `i != j`, then `S_w <= t_c pi(P_i) t_c^-1` and
`S_v <= t_c pi(P_j) t_c^-1`, which commute by (TL1).  If `v = w x` with `x`
nonempty, then `S_v = t_w S_x t_w^-1 <= t_w pi(P_(x_1)) t_w^-1`, while
`S_w = t_w pi(S) t_w^-1`, and `pi(S)` commutes with `pi(P_(x_1))`.

**(TL4).**  Each `S_w` is isomorphic to `S` because `pi|_S` is injective, so it
is nonabelian and centerless.  The kernel `N` of the multiplication map is
normal in the direct sum and meets every summand trivially.  If `n in N` has
component `n_w != 1`, choose `a in S_w` with `[n_w,a] != 1`.  Then
`[n,a] = [n_w,a]` lies in `N cap S_w = 1`, a contradiction.

**(TL6).**  `u_i^-1 S u_i` commutes with `u_i^-1 P_i u_i = P` in `E`.

**(TL7).**  `pi(S)` commutes with `B = alpha_1(Gamma) alpha_2(Gamma)`, so
`pi(S) cap B` is central in the centerless group `pi(S)`, hence trivial.  The
intersection `alpha_1(Gamma) cap alpha_2(Gamma)` commutes with both factors.

**Properness.**  If `Gamma = pi(S) B`, then `Gamma` is the direct product
`pi(S) x B`, so `S` is a quotient of the Kazhdan group `Gamma` and is Kazhdan.
A group acting on a tree without a global fixed point is not Kazhdan
(Watatani).

**Regular models.**  The trace restricted to `(+)_w S_w` is the regular
character, so the generated algebra is the restricted infinite tensor
product of the `L(S_w)`.  Each factor is a II_1 factor because an infinite
simple group has infinite conjugacy classes.  `Ad u(t_i)` carries
`u(S_w)` onto `u(S_(iw))` by (TL5).
