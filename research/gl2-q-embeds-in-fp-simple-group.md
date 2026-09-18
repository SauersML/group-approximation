---
rg: 2
id: gl2-q-embeds-in-fp-simple-group
kind: claim
title: GL_2(Q) embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is every n >= 2, which implies this (route gl2-q-bh-via-root); this is the case n = 2 alone.
  sl2-q-embeds-in-fp-simple-group: that is the determinant-one subgroup SL_2(Q), which this implies.
  psl2-q-embeds-in-fp-simple-group: that is PSL_2(Q), a quotient of a subgroup of GL_2(Q); neither statement is known to imply the other.
  gl-n-q-targets-are-cofinal-in-n: that compares the cases for different n; this is the single case n = 2.
---

**OPEN.** There is a finitely presented simple group containing `GL_2(Q)`.

This is the `n = 2` case of `gl-n-q-embeds-in-fp-simple-group` (BBMZ
arXiv:2306.16356v3, Problem 5.3(5); route `gl2-q-bh-via-root`). It implies
`sl2-q-embeds-in-fp-simple-group` (route `sl2-q-bh-via-gl2`). It also implies
the same statement for the stepping stones `Aff(Q) = {[[a,b],[0,1]]}` and the
Borel subgroup `B_2(Q)`, which are subgroups of `GL_2(Q)`.

## Structure

- **Into a countable simple group.** `g ↦ diag(g, det(g)^-1)` embeds `GL_2(Q)`
  in `SL_3(Q)`. The centre of `SL_3(Q)` consists of the scalars `ζI` with
  `ζ^3 = 1`, `ζ ∈ Q`, so it is trivial, and `SL_3(Q) = PSL_3(Q)` is simple.
  So the `n = 3` case of the root implies this claim, as recorded in
  `gl-n-q-targets-are-cofinal-in-n`.
- **Subgroups that constrain hosts.** It contains everything listed for
  `SL_2(Q)`. It also contains `BS(1,2) = <x ↦ x+1, x ↦ 2x> <= Aff(Z[1/2])`,
  which is exponentially distorted, and the countable abelian `Q^x`.

## Host status

The same as for `sl2-q-embeds-in-fp-simple-group`:
- residually finite groups, `V`, `T-bar`, `A`, `VA` and Q-free lifts are
  excluded;
- natural piecewise-projective actions are excluded;
- fixed-point arguments exclude nothing (`gl2-q-fa-subgroups-are-finite`);
- `nV`, twisted Brin--Thompson groups and germ extensions with distorted germs
  are not excluded here.

## Attempts

See `sl2-q-embeds-in-fp-simple-group`, Attempts 1--3. They apply verbatim.
