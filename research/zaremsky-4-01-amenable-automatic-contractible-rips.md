---
rg: 2
id: zaremsky-4-01-amenable-automatic-contractible-rips
kind: claim
title: "Zaremsky Problem 4.1 resolved: does every amenable automatic group have a contractible Rips complex?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is the question for Z^n with its standard word metric, answered by Virk; this is the question for every amenable automatic group, over any finite generating set and scale
  hyperbolic-rips-complex-models-proper-actions: that is the classical theorem that large-scale Rips complexes of hyperbolic groups model proper actions; this asks for a contractible Rips complex of every amenable automatic group
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4 (Vietoris–Rips
complexes), Problem 1, verbatim: "If a group is amenable and automatic, does it
have a contractible Rips complex? (This would show that F cannot be both
amenable and automatic.)"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-01-by-yes` requires
  `amenable-automatic-groups-have-contractible-rips-complexes`.
- **No**: `zaremsky-4-01-by-no` requires
  `some-amenable-automatic-group-has-no-contractible-rips-complex`.

Never write a `requires: []` route into this claim.

## Reading

- **Rips complex.** For a finitely generated group `G`, a finite generating set
  `S` with word metric `d_S`, and `r >= 0`, the Rips complex `P_r(G,S)` is the
  simplicial complex with vertex set `G` whose simplices are the finite
  nonempty subsets of `d_S`-diameter at most `r`. It is locally finite and
  finite-dimensional, since a simplex containing `1` lies in the ball
  `B_S(r)`, and `G` acts on it by left multiplication, properly and
  cocompactly.
- **"Has a contractible Rips complex"** is read existentially: there are `S`
  and `r` with `P_r(G,S)` contractible. Because `d_{B_S(r)}(x,y) <= 1` iff
  `d_S(x,y) <= r`, we have `P_1(G, B_S(r)) = P_r(G,S)`. So the reading is
  equivalent to: some Cayley graph of `G` over a finite generating set has a
  contractible clique complex.
- **Stronger reading.** A fixed `S` with `P_r(G,S)` contractible for all
  sufficiently large `r` ("type R" in Li–Sánchez Saldaña, arXiv:2608.24279),
  as in Problems 4.3 and 4.5. The parenthetical consequence needs only the
  existential reading, so the answer claims use it.
- **Automatic** is in the sense of Epstein, Cannon, Holt, Levy, Paterson and
  Thurston, *Word Processing in Groups* (1992); see
  `zaremsky-2-02-thompson-f-automatic` for the definition. It does not depend
  on the finite generating set. **Amenable** means there is a left-invariant
  mean on `G`.

## Why the parenthetical holds

A torsion-free group with a contractible Rips complex has a finite `K(G,1)`
(`contractible-rips-complex-gives-finite-classifying-space`). `F` is torsion-free of
infinite cohomological dimension, so no Rips complex of `F` is contractible
(`thompson-f-has-no-contractible-rips-complex`). A yes answer therefore gives
`thompson-f-is-not-both-amenable-and-automatic` (route
`thompson-f-not-amenable-and-automatic-via-rips`), and more precisely
`thompson-f-is-not-automatic` if `F` is amenable and
`thompson-f-is-not-amenable` if `F` is automatic.

## Known cases (bounded check, 2026-09-13)

- Hyperbolic groups have contractible Rips complexes at large scale
  (`hyperbolic-rips-complex-models-proper-actions`). Amenable hyperbolic groups
  are virtually cyclic.
- `Z^n` with its standard generators (Virk,
  `rips-complexes-of-integer-lattices-are-contractible`).
- Products of finitely generated free abelian groups and finite groups are of
  type R (Li–Sánchez Saldaña, arXiv:2608.24279, from the abstract).
- Nilpotent automatic groups are virtually abelian (Epstein et al., Chapter 8;
  theorem number not re-read here). Whether every amenable, or every solvable,
  automatic group is virtually abelian was not settled by this lane's search.

Search bounds: the arXiv search for "contractible Rips complex" returns only
arXiv:2608.24279; the lane's web-search budget was exhausted and MathSciNet was
not reached. No answer to Problem 4.1 was found.

## Attempts

- 2026-09-13 (lane z4-01-amen-auto-rips): **the hyperbolic template.** Rips's
  proof pushes the vertex of a simplex that is farthest from `1` one step back
  along a geodesic, and thin triangles keep the pushed simplex inside
  `P_r(G,S)`. For an automatic structure, synchronous fellow travelling bounds
  the distance between truncated normal forms of `r`-close elements only by a
  constant multiple `K r` of `r`, so the pushed simplex leaves `P_r(G,S)`. The
  combing gives only maps from `P_r` into `P_{Kr}`, a coarse statement that
  does not produce one contractible complex, and the argument never uses
  amenability.
- 2026-09-13: **what a yes answer must contain.** By
  `contractible-rips-complex-gives-finite-classifying-space`, it would show every
  torsion-free amenable automatic group is of type F. For the consequence about
  `F` the weaker statement "torsion-free amenable automatic groups have finite
  cohomological dimension" already suffices.
