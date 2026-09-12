---
rg: 2
id: leavitt-tower-does-not-embed-in-torsion-free-hosts
kind: claim
title: No group of the Leavitt tower embeds in a torsion-free group, in particular not in the Fournier-Facio group
distinct_from:
  leavitt-surjunctivity-tower: that orders Thompson V and the binary and d-ary Leavitt unit groups by inclusion and transports surjunctivity along it; this says no member of that tower embeds in any torsion-free group.
  fournier-facio-outside-surjunctivity-permanence: that records the Fournier-Facio group's surjunctivity as open and outside permanence; this settles one direction of its embedding relation with the Leavitt tower.
artifacts:
  - research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)`. The unit `u = 1 + s_0 t_1` satisfies
`u != 1` and `u^2 = 1`, because `t_1 s_0 = 0` and the characteristic is two.
Thompson's `V` contains every finite symmetric group, and the d-ary Leavitt unit
groups over `F_2` contain `R^x` (`leavitt-surjunctivity-tower`). So every group of
the tower `V <= R^x <= A^x` has elements of order two, and none embeds in a
torsion-free group. In particular none embeds in the Fournier--Facio group of
`fournier-facio-torsion-free-skeleton`.

Consequences:

- A strict automaton on `R^x` does not ascend to the Fournier--Facio group, so the
  two counterexample searches are independent in this direction.
- Whether the Fournier--Facio group embeds in `R^x` is not decided here. If it
  did, a strict automaton on it would ascend to `R^x`.

Proof: `leavitt-tower-does-not-embed-in-torsion-free-hosts-proof`.
