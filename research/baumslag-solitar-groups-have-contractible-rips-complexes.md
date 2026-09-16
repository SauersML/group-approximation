---
rg: 2
id: baumslag-solitar-groups-have-contractible-rips-complexes
kind: claim
title: Every Baumslag–Solitar group BS(m,n) has a contractible Rips complex at scale 1, from a staircase triangulation of its presentation complex
distinct_from:
  every-type-f-group-has-a-contractible-rips-complex: that is the universal affirmative answer to Zaremsky Problem 4.7; this settles the Baumslag–Solitar family only, with an explicit generating set
  virtually-abelian-groups-have-contractible-rips-complexes: that covers BS(1,1) and BS(1,-1); this covers every BS(m,n), including the solvable BS(1,n) with |n| >= 2 and the non-Hopfian ones
  rips-type-r-closed-under-finite-edge-group-splittings: that handles splittings over finite groups with union generating sets; BS(m,n) is an HNN extension over infinite cyclic subgroups, and this gives a single scale-1 complex, not type R
  helly-groups-have-contractible-rips-complexes: that builds contractible Cayley clique complexes from geometric actions on Helly graphs; this triangulates a one-relator presentation complex and identifies the triangulation with a clique complex
artifacts:
  - research/artifacts/baumslag-solitar-contractible-rips-2026-09-16.md
---

Let `m, n` be nonzero integers and `G = BS(m,n) = <a, t | t a^m t^-1 = a^n>`.
Assume `m >= 1`; this loses nothing, since `a -> a^-1` gives
`BS(m,n) ≅ BS(-m,-n)`. Put `N = |n|` and `δ = sign(n)`.

Let `P` be any monotone lattice path from `(0,0)` to `(m,N)`, with unit steps
`(1,0)` or `(0,1)`. Put `s(r,i) = a^(-δi) t a^r` and

`S = {a^±1} ∪ {s(r,i)^±1 : (r,i) ∈ P}`.

**Claim.**
- `S` is a finite symmetric generating set of size `2 + 2(m+N)`.
- The clique complex `Flag(Cay(G,S))`, which is the Rips complex
  `R_1(G, d_S)`, is contractible.
- It is 2-dimensional and equals the triangulation of the universal cover of
  the presentation complex of `<a,t | t a^m t^-1 a^-n>` obtained by cutting
  each relator polygon along the chords `t a^r — a^(δi)`, `(r,i) ∈ P`.

Example: for `BS(1,2)`, the path `(0,0),(0,1),(0,2),(1,2)` gives
`S = {a^±1, t^±1, (a^-1 t)^±1, (a^-2 t)^±1}`.

**Why it matters here.** `some-type-f-group-has-no-contractible-rips-complex`
and `zaremsky-4-07-type-f-groups-have-contractible-rips` name `BS(1,2)` as a
test object for a counterexample to Zaremsky Problem 4.7. This claim rules
out `BS(1,2)` and the whole family. Several features therefore cannot be what
obstructs a contractible Rips complex:
- an exponential Dehn function;
- non-automaticity;
- exponentially distorted cyclic subgroups;
- non-Hopficity.

Whether the family was already covered by another class in the graph, for
example contracting combings, was not checked. No source stating this result
was found in the 2026-09-16 literature gate.
