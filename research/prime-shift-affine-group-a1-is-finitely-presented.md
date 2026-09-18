---
rg: 2
id: prime-shift-affine-group-a1-is-finitely-presented
kind: claim
title: The prime-shift permutation group A_1 = <x+1, 2x, -x, σ> of Q is finitely presented
distinct_from:
  prime-shift-hnn-groups-are-not-finitely-presented: that proves the HNN group Π_1 is not finitely presented and that finite presentation of A_1 needs a hidden relation; this asks whether A_1 itself is finitely presented.
  prime-shift-hnn-map-to-a1-is-injective: that asks whether Π_1 -> A_1 is injective; a positive answer there refutes this claim.
  prime-shift-affine-group-a1-has-fg-point-stabilizer: that is the other type (A) condition, on a point stabilizer; this is the finite-presentation condition.
---

**OPEN.** The group `A_1 = <x -> x+1, x -> 2x, x -> -x, σ> <= Sym(Q)` of
`gl-n-q-lies-in-prime-shift-permutation-group` is finitely presented.

**Source.** Root `gl-n-q-embeds-in-fp-simple-group`, Attempt 18: for `A_1`, type (A) "reduces to finite
presentation plus one finitely generated point stabilizer; both are OPEN."

**Known.**
- `prime-shift-hnn-groups-are-not-finitely-presented`, item 2: if `A_1` is finitely presented, then some
  dilation `m_r`, with `r` in `Q_>0` and `r != 1`, lies in the normal closure of `x -> x+1` in `A_1`. In that
  case `Π_1 -> A_1` is not injective.
- Together with `prime-shift-affine-group-a1-has-fg-point-stabilizer`, this claim makes the action of `A_1`
  on `Q` a type (A) action. That puts `Aff(Q)` in a finitely presented simple group (route
  `aff-q-bh-via-prime-shift-type-a-action`).

## Attempts

None recorded as a separate node; see root Attempt 18 (lane gq-deep-typeA-2).
