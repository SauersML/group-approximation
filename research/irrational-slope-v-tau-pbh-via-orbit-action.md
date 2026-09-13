---
rg: 2
id: irrational-slope-v-tau-pbh-via-orbit-action
kind: route
title: V_τ has a type (A) orbit action once it is finitely presented
target: irrational-slope-v-tau-subgroups-satisfy-pbh
requires:
  - pl-rearrangement-groups-have-two-transitive-orbit-actions
  - irrational-slope-t-tau-and-v-tau-are-finitely-presented
---

**The model.** Burillo--Nucinkis--Reeves define `V_τ` as the left-continuous
piecewise-linear bijections of `(0,1]` with breakpoints in `Z[τ]` and slopes powers of
`τ` (arXiv:2006.02401, l.111). Conjugation by `x ↦ 1 − x` turns a left-continuous
increasing affine piece on `(a,b]` into a right-continuous increasing affine piece on
`[1−b, 1−a)` with the same slope. Breakpoints move by `x ↦ 1 − x`, which preserves
`Z[τ]`, and constants stay in `Z[τ]`. So `V_τ ≅ V(Z[τ], <τ>)` in the notation of
`pl-rearrangement-groups-have-two-transitive-orbit-actions`. `T_τ` is the subgroup of
circle homeomorphisms, cut open at `0`, and contains `F_τ`.

**Hypotheses.** The target of that node checks them for `A = Z[τ]` and `P = <τ>`:
`τ` is a unit with `1 = τ + τ²`, and every positive element of `Z[τ]` is a finite sum of
powers of `τ`, via the Fibonacci–Binet argument.

**Proof.** By `irrational-slope-t-tau-and-v-tau-are-finitely-presented`, `V_τ` is
finitely presented. So by part 3 of `pl-rearrangement-groups-have-two-transitive-orbit-actions`,
the action on `Z[τ] ∩ [0,1)` is of type (A), and every subgroup of `V_τ` satisfies
permutational Boone--Higman, has solvable word problem, and embeds in a finitely
presented simple group. ∎
