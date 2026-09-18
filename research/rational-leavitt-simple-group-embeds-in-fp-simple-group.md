---
rg: 2
id: rational-leavitt-simple-group-embeds-in-fp-simple-group
kind: claim
title: The countable simple group L_Q(1,2)^x / Q^x embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for one n at a time; this asks for one countable simple group containing GL_∞(Q), hence every GL_n(Q) at once, together with Thompson's V.
  leavitt-unit-groups-over-every-field-are-simple-mod-scalars: that proves the group simple; this asks for a finitely presented simple overgroup.
  odd-leavitt-unit-groups-mod-scalars-are-fp-simple: that is the finite prime fields, where the scalar quotient is itself finitely presented; over Q it is not even finitely generated.
---

**OPEN.** Let `Λ = L_Q(1,2)^x / Q^x`. There is a finitely presented simple group `S` and
an injective homomorphism `Λ -> S`.

**Why it is a natural target.**
- `Λ` is a countable simple group containing `GL_∞(Q)`, `V` and `SL_3(Z)`
  (`leavitt-unit-groups-over-every-field-are-simple-mod-scalars`). So this claim
  gives `gl-n-q-embeds-in-fp-simple-group` for every `n` at once, through the route
  `gl-n-q-bh-via-rational-leavitt-simple-group`.
- **Conditional on Boone–Higman.** `Λ` has solvable word problem for the enumeration
  of its elements by normal forms of units: products are computed in normal form, and
  being a scalar is read off from the normal form. So `boone-higman-conjecture` implies
  this claim, by survey Corollary 3.5.

**Constraints on any host** (from landed nodes):
- `S` contains `SL_3(Z)`, so it is neither `V` nor `VA` (root, O2).
- `S` contains `(Q,+)`, so no residually finite group lies between `Λ` and `S` (root,
  O1).
- No finitely generated subring of a Leavitt algebra over a field contains `Q`
  (`infinite-field-leavitt-units-are-not-finitely-generated`, part 3). So `S` cannot be
  a unit group of a Leavitt algebra over a commutative coefficient ring. `Q` has to
  enter through noncommutative coefficients or another mechanism.

## Attempts

1. **Scalar-coefficient Leavitt hosts over S-integers.** Every finitely generated
   subgroup of `L_Q(1,2)^x` lies in some `L_(Z[1/m])(1,2)^x`, and `Λ` is the ascending
   union of their images. These groups have congruence quotients
   (`char-zero-leavitt-unit-groups-have-congruence-kernels`), and whether they are
   finitely presented is open (`leavitt-units-over-s-integers-are-finitely-presented`).
   Even a positive answer gives only an ascending union of finitely presented groups,
   not one finitely presented overgroup.
