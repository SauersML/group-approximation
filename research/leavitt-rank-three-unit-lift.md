---
rg: 2
id: leavitt-rank-three-unit-lift
kind: claim
title: Three units suffice to lift each Leavitt generator into the group algebra
distinct_from:
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the qualitative spanning statement, which gives no bound on how many units an element needs; this pins the number at three for the two generators that carry the defect, by a self-similarity computation the spanning proof does not perform.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies GL with EL over the Leavitt algebra and proves the unit group perfect; this counts how many units it takes to write one non-unit additively, a question about the additive structure that says nothing about the group.
  leavitt-unit-group-algebra-not-directly-finite: that is the open failure of direct finiteness; this is an established construction of two specific short elements of the group algebra, and their product is explicitly not claimed to be 1.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

There are units `u_1, u_2, u_3` and `v_1, v_2, v_3` of `R = L_(F_2)(1,2)`,
each triple pairwise distinct and given in closed form, with

    t_0 = u_1 + u_2 + u_3,      s_0 = v_1 + v_2 + v_3.

Hence `t~ = [u_1] + [u_2] + [u_3]` and `s~ = [v_1] + [v_2] + [v_3]` in
`F_2[R^x]` have support **exactly three**, with `pi(t~) = t_0`,
`pi(s~) = s_0`, and therefore `pi(t~ s~) = t_0 s_0 = 1`.

The last equation holds only after applying `pi`.  The formal product
`t~ s~` in the group algebra is not `1` and nothing here says it is; this
claim supplies lifts of the *generators*, not of the relation.

The units come from the self-similarity `R = M_2(R)` and a
characteristic-two identity writing any `2x2` matrix as a sum of three
elementary-type units, so the count three is what that identity gives, not a
proved minimum.  Whether the Leavitt generators admit lifts of support one or
two is not decided here; support one would make `t_0` a unit, which
`binary-leavitt-algebra-not-directly-finite` forbids.

Its use was `leavitt-rank-three-lift-inverse-support-thirteen`: fixing the
rank of the lift at three is what lets the bounded-rank computations of
`dykema-heister-juschenko-bounded-rank-direct-finiteness` apply, and they then
push any completing one-sided inverse out to support at least thirteen.

**What the three units turned out to be (2026-08-18).**  They generate a free
product `(C_2 x C_2) * C_3`, and so do `v_1,v_2,v_3`
(`leavitt-rank-three-support-group-is-virtually-free`); moreover the shared
third unit `u_3 = v_3` is exactly the order-three unit
`g = (1+s_0t_1)(1+s_1t_0)` of `leavitt-corner-idempotent-unital-surjection`,
so the corner idempotent `e = [g]+[g^2]` lies in the same group algebra
`F_2[<u_1,u_2,u_3>]`.  That is fatal for both lifts:
`leavitt-rank-three-lift-has-no-one-sided-inverse` shows neither `t~` nor `s~`
nor `e t~ e` can be completed, at any support.  This claim is unaffected — it
only ever asserted the additive splitting, and was explicit that the product
is not `1` — but its downstream use has changed from "bound the completion" to
"there is no completion".
