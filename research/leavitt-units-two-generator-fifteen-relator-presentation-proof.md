---
rg: 2
id: leavitt-units-two-generator-fifteen-relator-presentation-proof
kind: route
title: Merge v and x into one element of order six by Tietze transformations
target: leavitt-units-two-generator-fifteen-relator-presentation
requires: [thompson-steinberg-three-generator-presentation]
artifacts:
  - experiments/nonsofic-certificates/presentations/verify_two_generator_presentation.py
  - experiments/nonsofic-certificates/presentations/two-generator-presentation.json
---

Let `Q3 = <u, v, x | R16>`, which is isomorphic to `L^x` by
`thompson-steinberg-three-generator-presentation`. Put `T = 1 + S[0000]T[001]`, and let `g` be a
word in `u, v` whose Thompson unit sends `00 -> 0000` and `01 -> 001`, so that
`T = ĝ x ĝ^-1`.

1. Add a generator `w` with the relator `w = v ĝ x ĝ^-1`. This gives a presentation of the same
   group.
2. In `L^x`, `v` fixes every point of the cone `00`, so it commutes with `T`. Also `v^3 = 1` and
   `T^2 = 1`. Hence `w^6 = 1`, `w^-2 = w^4 = v` and `w^3 = T`, so `x = ĝ^-1 w^3 ĝ`. These
   identities hold in `L^x`, so they are consequences of the complete relator set `R16`. Add them
   as relators.
3. Eliminate `v` and `x` by these relators: substitute `v -> w^-2` and `x -> G^-1 w^3 G`, where `G`
   is `g` with `v -> w^-2`, into every relator. The defining relators become trivial. What remains
   is `R16` with the substitution.
4. The substituted `x^2` is `G^-1 w^6 G`, a conjugate of the inverse of the substituted `v^3`,
   which is `w^-6`. So it is redundant.

This leaves fifteen relators on `u, w`. QED.

The exact check (MSI, PASS) confirms the identities consumed in step 2 in dual mode:
`[v,T] = 1`, `w^6 = 1`, `w^-2 = v`, `G^-1 w^3 G = x`. All fifteen substituted relators hold in
`L^x`, and the negative controls `[u,w]`, `w^3`, `w^2` are nontrivial. The BFS conjugator is
`g = u v^-1 u^-1 v u^2 v^-1 u^-1 v^-1`. It was the shortest in total length among four cone
choices inside `00`.
