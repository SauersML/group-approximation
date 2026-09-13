---
rg: 2
id: fp-simple-irs-via-labbe-shift
kind: route
title: A finitely presented derived full group of Labbé's shift has a nontrivial ergodic IRS
target: fp-infinite-simple-group-with-nontrivial-irs
requires:
  - minimal-aperiodic-wang-shift-exists
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - labbe-shift-derived-full-group-is-finitely-presented
---

Let `S = D([[Z^2 ~ Omega_U]])`. It is infinite and simple
(`minimal-z2-subshift-derived-full-groups-are-fg-simple`), and finitely presented by
the third prerequisite.

**The action.** `Z^2` is amenable and acts on the compact space `Omega_U`, so an
invariant probability measure exists (Markov--Kakutani). Choose an ergodic one, `mu`,
which exists as an extreme point of the simplex of invariant measures. By minimality
it has full support. Each element of `S` is a piecewise `Z^2`-translation with finitely
many clopen pieces, so `S` preserves `mu`. The `S`-orbits coincide with the
`Z^2`-orbits: `D([[Omega_U]])` contains every 3-cycle of translated cylinders, and
such 3-cycles move any point to any other point of its `Z^2`-orbit. So
`mu` is `S`-ergodic.

**Nontrivial IRS.** Let `nu = Stab_* mu` on `Sub(S)`. It is ergodic because `mu` is.
- `nu != delta_S`: a nontrivial element moves a nonempty open set, which has positive
  measure.
- `nu != delta_{1}`: freeness of `Z^2` and aperiodicity give a clopen set `U` with
  `U`, `U + e_1`, `U + 2e_1` pairwise disjoint. The corresponding 3-cycle lies in `S`
  and fixes the complement of `U ∪ (U + e_1) ∪ (U + 2e_1)`, which has positive measure
  when `U` is small.

So `S` witnesses `fp-infinite-simple-group-with-nontrivial-irs`. ∎

**On the orbit claim.** For `x` in a `Z^2`-orbit and `y = n x`, a 3-cycle on small
clopen neighbourhoods of `x` and `n x`, with a third translate, maps `x` to `y`. The
neighbourhoods can be chosen pairwise disjoint because the action is free. So
`S x = Z^2 x`, and every `S`-invariant Borel set is `Z^2`-invariant.
