---
rg: 2
id: some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f
kind: claim
title: "Some subgroup of Thompson's group F is not elementary amenable and contains no copy of F (negative answer to Brin–Sapir)"
distinct_from:
  every-subgroup-of-thompson-f-is-ea-or-contains-f: that is the affirmative answer; this is its negation, a counterexample subgroup.
---

There is a subgroup `H` of Richard Thompson's group `F` that is not elementary
amenable and has no subgroup isomorphic to `F`. This is the negative answer to
Zaremsky Problem 2.3 (`zaremsky-2-03-brin-sapir-conjecture`), and it is the
negation of `every-subgroup-of-thompson-f-is-ea-or-contains-f`.

A counterexample can be taken finitely generated: if every finitely generated
subgroup of `H` were elementary amenable, `H` would be too, as their directed union.

## Attempts

- **Constraints on a counterexample (z2-03-brin-sapir, 2026-09-13; each piece
  established, unreviewed).** A finitely generated counterexample `H`:
  - has synchronized end germs on every orbital of every subgroup
    (`f-free-plo-i-groups-have-equal-end-germ-kernels`);
  - carries an infinite compactly nested descent `(D_i, A_i)` of finitely generated
    non-elementary-amenable subgroups, each inside the germ-trivial kernel of the
    previous one on a nested orbital
    (`plo-i-group-is-ea-iff-its-orbital-germ-kernels-are`, part 5);
  - has no two one-bump elements with different supports that overlap, share
    exactly one endpoint, or are nested with some translate of the smaller support,
    under the larger element, meeting it
    (`two-one-bump-pl-maps-unequal-supports-ea-or-contain-f`).
- **Self-similar nesting (idea, untested).** Bleak–Brin–Moore's groups `G_ξ`,
  `ξ < ε_0` (`f-has-ea-subgroups-of-every-class-below-epsilon-zero`), are all
  elementary amenable. A counterexample needs a configuration whose germ-kernel
  descent never stops, realized with finitely many breakpoints per generator. Where
  it dies so far: making a subgroup reappear inside its own compactly supported
  kernel, by conjugating with an element of the group, tends to produce either an
  element approaching one end of an orbital but not the other, or two one-bump
  conjugates in overlapping position; either gives a copy of `F`. Not yet a proof of
  anything.
