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

- **Constraints on a counterexample (2026-09-13, z2-03-brin-sapir).** A finitely
  generated counterexample `H` has, on every orbital, germ kernels at the two ends
  that coincide (Brin 1999, Theorem 1, contrapositive), and it carries an infinite
  compactly nested sequence of finitely generated non-elementary-amenable
  subgroups, each inside the germ kernel of the previous one on a nested orbital.
  So a construction must nest non-elementary-amenable complexity inside compactly
  supported kernels infinitely often, while keeping, on every orbital of every
  subgroup, slope germs at both ends synchronized.
- **Self-similar nesting of Bleak–Brin–Moore signatures (idea, untested).** Their
  groups `G_ξ` (`ξ < ε_0`, arXiv:1711.10998) are all elementary amenable. A
  counterexample would need a self-referential configuration, realized with
  finitely many breakpoints per generator, whose kernel tower never terminates.
  Where it dies so far: an internal self-similarity (an element of the group
  conjugating the configuration into a proper compact part of itself) tends to
  create an element approaching one end of an orbital but not the other, which
  yields a copy of `F` by Brin's criterion. Not yet a proof of anything.
