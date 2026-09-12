---
rg: 2
id: leavitt-unit-linear-soficity-is-ring-rank-approximability
kind: claim
title: The Leavitt unit group is linear sofic iff its Leavitt algebra is rank-approximately representable
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that is the exact statement that no unital ring homomorphism R sends into a rank ultraproduct; this is the approximate group-side equivalence, whose gap from the exact statement is whether the isometries can be approximately proper.
  binary-leavitt-unit-group-is-f2-linear-sofic: that is the open positive gate itself; this reframes it as an algebra-approximation property of R.
  rank-four-isometry-relations-give-corner-cuntz-family: that is the operator assembly closing the gate; this is the equivalent restatement of the gate as ring rank-approximability.
artifacts:
  - research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md
---

**OPEN.** Let `R = L_K(1,2)`, `K` finite of characteristic `p`. Then `R^x` is `F_p`-linear sofic if
and only if `R` is **rank-approximately representable**: for every finite `F ⊂ R` and `eps > 0`
there are `n` and a unital `F_p`-linear map `phi : R -> M_n(F_p)` with

```text
rk( phi(ab) - phi(a) phi(b) ) < eps  (a, b in F),      rk( phi(x) ) > c > 0  (x in F, x != 0),
```

with `c` independent of `F, eps`, and `phi` respecting the Leavitt relations up to rank `eps`.

## Why this is the right reframing

The exact form -- a unital ring homomorphism `R` into a rank ultraproduct -- is impossible by
`leavitt-algebra-has-no-unital-rank-model`, because a rank ultraproduct is stably finite and the
isometries cannot be proper (`t_i s_i = 1` forces `s_i t_i = 1`, killing `1 - s_i t_i`). This node
isolates the entire remaining question: whether the **approximate** relations can hold with the
isometries **approximately proper**, `rk(t_i s_j - delta_ij) -> 0` while `rk(1 - s_i t_i)` stays
bounded below. That gap is exactly the gate.

## Attempts

- **Forward.** A linear sofic model of `R^x = EL_2(R)` restricts on the `(1,2)` root subgroup to a
  map `a |-> phi(a)` recovering an approximate representation of `(R, +)`; the Steinberg relation
  `[x_12(a), x_21(b)]` carries the multiplication, giving approximate multiplicativity.
- **Backward.** `GL_n(R) = EL_n(R) = R^x` (`leavitt-gl-equals-el-and-perfect-unit-group`) amplifies
  a rank-approximate `phi` to a group model, so ring rank-approximability implies linear soficity.
- **Use.** Converts the gate to a characteristic-uniform algebra-approximation statement. Plan 1
  (`rank-four-isometry-relations-give-corner-cuntz-family`) predicts it is FALSE: the four-index
  assembly would turn any bounded-below approximate model into an exact corner Leavitt family.
- **Open.** The exact constants in the forward and backward directions, and whether "approximately
  proper isometries" can persist in the rank metric at all.
