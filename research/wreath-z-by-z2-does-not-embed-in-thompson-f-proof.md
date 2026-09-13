---
rg: 2
id: wreath-z-by-z2-does-not-embed-in-thompson-f-proof
kind: route
title: Bump orbits have nonzero stabilizers that fix the lamp, so a nonzero group-ring element kills it
target: wreath-z-by-z2-does-not-embed-in-thompson-f
requires: []
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part1.md
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part2.md
---

Full derivation in part 2 of the artifact (Steps 1–5), using Lemmas A and B of part 1.
Summary, with `Q = Z^2 = <s,t>` and lamp `a`:

1. Bumps of the commuting lamps `a_v = v a v^{-1}` are pairwise equal or disjoint.
   `Q` permutes them, and the base group preserves each one.
2. Every bump `B` of `a` has a nonzero stabilizer in `Q`. If not, `B` lies in a common
   bump `K` of `s` and `t`, and the slope homomorphism `Q → Z` at the left endpoint of
   `K` has a nonzero kernel element `c`. By germ determination `c = id` on `K`, so `c`
   fixes `B`.
3. For `v` in the stabilizer of a bump orbit, `a_v = a` on that orbit (equal slopes at a
   common fixed endpoint, then germ determination).
4. Choose a nonzero stabilizer element `v_i` on each of the finitely many orbits met by
   the bumps of `a`. Then `f = ∏ (1 − x^{v_i})`, a nonzero element of the domain
   `Z[Z^2]`, kills `a`. This contradicts the freeness of the base module.
