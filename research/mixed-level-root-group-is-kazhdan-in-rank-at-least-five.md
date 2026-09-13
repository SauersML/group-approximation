---
rg: 2
id: mixed-level-root-group-is-kazhdan-in-rank-at-least-five
kind: claim
title: The mixed-level root subgroup K_i of EL_r(F_q[x_1..x_d]) has property (T) for every r at least five
---

**ESTABLISHED.** Let `R` be a finitely generated commutative unital ring, `t ∈ R`, and `r >= 5`. For `c ≠ d`
put

```text
eps_cd = [c = 3] + [d = 2],      I_cd = t^(eps_cd) R.
```

So row 3 and column 2 sit at level `(t)`, the corner `(3,2)` at level `(t^2)`, and every other root, including
`(2,3)`, is full. Let

```text
K = K(R, t) = < e_cd(I_cd) : c ≠ d >  <=  EL_r(R).
```

Then `K` has property (T): some finite subset of `K` is a Kazhdan set.

**Use.** For `R = F_q[x_1..x_d]` and `t = x_i` this is the group `K_i` of `laurent-vertex-rounds-for-every-model`
(Attempts, lane `nh-laurent-commutant`). The reduction recorded there then gives the converse Laurent direction
on `St_r(L)` for every `r >= 5`, including the Kun–Thom instance `r = 6`.

**Rank four is sharp.** The proof needs three blocks meeting `J = {1..r} \ {2,3}` and pivots inside `J`. At
`r = 4`, `|J| = 2`, and for `d >= 2` the conclusion fails (`mixed-level-root-group-is-not-kazhdan-in-rank-four`).
The EJZK criterion does apply when some root subgroups are proper ideals, provided each level ideal is the
product of two levels through a full index.
