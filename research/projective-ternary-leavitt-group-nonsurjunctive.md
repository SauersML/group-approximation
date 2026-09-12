---
rg: 2
id: projective-ternary-leavitt-group-nonsurjunctive
kind: claim
title: The ternary Leavitt unit group modulo scalars is not surjunctive
root: true
distinct_from:
  ternary-leavitt-unit-group-nonsurjunctive: that is the unit group itself, a central extension of this group by its two scalars, which also embeds in this group through a corner homomorphism; so nonsurjunctivity passes from that group to this one, and the converse is not known.
  leavitt-unit-group-nonsurjunctive: that is the binary unit group over F_2, which has trivial scalars; this is a different finitely presented simple group in characteristic three.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** Exhibit a finite alphabet and an injective, non-surjective cellular
automaton over `PG = L_(F_3)(1,2)^x / F_3^x`. Such an automaton refutes
Gottschalk's conjecture (`gottschalk-surjunctivity-conjecture`).

*Marked `root` because it heads a counterexample lane on its own host, as
`leavitt-unit-group-nonsurjunctive` does.*

## Attempts

- *Linear invariant output.* Reduced to `projective-ternary-swap-idempotent-is-full`.
  That equation is implied by the unit-group equation
  `ternary-leavitt-swap-idempotent-is-full`, and it is the only part of that
  equation the full shift sees. It holds in the adjoint image algebra; the witnesses
  are open.
- *Host soficity, settled.* A sofic `PG` would be surjunctive by Gromov--Weiss, but
  `PG` is nonsofic (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`): it
  contains the unit group through the corner homomorphism.
- *Ascent from the unit group.* The same embedding makes any strict automaton on
  `L_(F_3)(1,2)^x` a strict automaton on `PG`
  (`ternary-unit-nonsurjunctivity-ascends-to-scalar-quotient`). So `PG` is the
  roomier host, and every construction over the unit group counts here.
