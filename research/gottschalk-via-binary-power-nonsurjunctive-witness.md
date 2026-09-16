---
rg: 2
id: gottschalk-via-binary-power-nonsurjunctive-witness
kind: route
title: Turn any strict automaton into a strict automaton over a binary-power alphabet on some group and use surjunctivity there
target: gottschalk-surjunctivity-conjecture
requires:
  - some-nonsurjunctive-group-gives-a-binary-power-one
  - every-group-is-surjunctive-over-binary-power-alphabets
---

1. Suppose some group `G` is not surjunctive over some finite alphabet `A`. Then `|A| >= 2`, since a one-point
   shift has only the identity map, so `|A| ∈ NS_all` and `NS_all` is nonempty.
2. By the first prerequisite, `2^j ∈ NS_all` for some `j >= 1`: some group `H` carries an injective, non-surjective
   cellular automaton on `B^H` with `|B| = 2^j`.
3. That contradicts the second prerequisite. So every group is surjunctive over every finite alphabet.

Both prerequisites are open. The first is implied by `nonsurjunctive-alphabet-sizes-are-upward-closed` and by
`some-nonsurjunctive-group-gives-a-binary-one`, so this route asks for less bridging than
`gottschalk-via-upward-closed-nonsurjunctive-sizes` and `gottschalk-via-universal-binary-descent`. It asks for
more than the second of those at the other prerequisite: binary-power surjunctivity implies binary surjunctivity.
