---
rg: 2
id: prime-shift-affine-group-a1-has-fg-point-stabilizer
kind: claim
title: The stabilizer of 0 in the prime-shift permutation group A_1 is finitely generated
distinct_from:
  prime-shift-affine-group-a1-is-finitely-presented: that is the finite-presentation condition of type (A) for A_1; this is the point-stabilizer condition.
  gl-n-q-lies-in-prime-shift-permutation-group: that constructs A_1 and reduces type (A) to these two conditions; this is the stabilizer condition as an open claim.
---

**OPEN.** `Stab_(A_1)(0)` is finitely generated. Here `A_1 = <x -> x+1, x -> 2x, x -> -x, σ> <= Sym(Q)` is
the group of `gl-n-q-lies-in-prime-shift-permutation-group`. `A_1` is transitive on `Q`, so all point
stabilizers are conjugate, and this is the point-stabilizer condition of type (A) for its action on `Q`.

**Source.** Root `gl-n-q-embeds-in-fp-simple-group`, Attempt 18, which also records that
`Stab_(A_1)(0)` is strictly larger than `Q^x ⋊ <σ>`.

**Use.** With `prime-shift-affine-group-a1-is-finitely-presented`, route
`aff-q-bh-via-prime-shift-type-a-action` puts `Aff(Q)` in a finitely presented simple group.

## Attempts

None recorded as a separate node; see root Attempt 18 (lane gq-deep-typeA-2).
