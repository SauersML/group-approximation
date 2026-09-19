---
rg: 2
id: nonhyperlinear-via-coherent-summable-clifford-tower
kind: route
title: Put every finite Clifford rank on one positive reducing carrier
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - coherent-summable-gap-clifford-tower
  - summable-reducing-carriers-force-infinite-clifford-capacity
---

Compile the fixed tracial/non-RU game into one finitely presented marked
group carrying the coherent tower. Exact tracial completeness supplies a
representation in which the marked word is nonidentity. If the group were
hyperlinear, choose one sufficiently accurate finite matrix microstate which
keeps that word separated. The coherent-tower estimate gives central or
jointly reducing carriers `C_N` with total discarded trace below one and the
first `N` Pauli cells exact on `C_N`.

The terminal capacity theorem intersects these carriers to a nonzero reducing
corner `C`. Its finite rank is divisible by `2^N` for every `N`, an
impossibility. Hence the marked word cannot have separating microstates and
the finitely presented group is nonhyperlinear.
