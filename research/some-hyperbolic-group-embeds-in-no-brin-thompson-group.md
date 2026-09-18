---
rg: 2
id: some-hyperbolic-group-embeds-in-no-brin-thompson-group
kind: claim
title: Some hyperbolic group embeds in no Brin-Thompson group nV
distinct_from:
  every-hyperbolic-group-embeds-in-some-brin-thompson-group: that is the affirmative answer to Zaremsky Problem 2.19(a); this is its negation, the negative answer.
  some-hyperbolic-group-does-not-embed-in-thompson-v: that excludes one hyperbolic group from V alone, through Farley's Haagerup theorem; this excludes a hyperbolic group from every nV at once, where no Haagerup theorem is known for n at least 2.
---

There is a finitely generated word-hyperbolic group `G` such that for every
`n ≥ 1` no homomorphism `G → nV` is injective. This is the negative answer to
Zaremsky Problem 2.19(a)
(`zaremsky-2-19a-every-hyperbolic-group-in-some-nv-resolved`).

## Candidates and the obstruction they need

- The natural candidates are infinite hyperbolic groups with property (T)
  (`torsion-free-hyperbolic-kazhdan-partner-exists`). No such group virtually
  embeds in a RAAG, so Belk–Bleak–Matucci does not apply to them.
- They embed in no nV if, for infinitely many n, every subgroup of nV with
  property (T), or more generally property FW, is finite.
- That finiteness follows from the Haagerup property of nV (Problem 2.7). It
  would also follow from a commensurated subset of an nV-set whose transfixing
  forces finiteness, as in the V case
  (`fw-subgroups-of-eventually-similar-groups-virtually-embed`).

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv, unreviewed): the V argument does not
  transfer through subcubes.
  - Let `C = {0,1}^ω`. The rearrangement of `C^2` that fixes `C×[0]` and swaps
    `[0]×[1]` with `[1]×[1]`, by changing the first digit of the first
    coordinate, sends `[w]×C` to `[w]×[0] ∪ [w']×[1]` with `w' ≠ w`.
  - So for every nonempty prefix `w`, the subcube `[w]×C` maps to a set that is
    not a subcube, and the set of subcubes is not commensurated.
  - The same failure blocks fat-subcube variants: an element with prefix-length
    change vector `s` moves infinitely many subcubes of minimal side exactly `L`
    to side `L + s_i < L`.
  - Weighted variants fail differently: nV does not preserve any weighting of
    subcubes by shape or volume, so they give no invariant measured wall
    structure.
  - The finiteness of Kazhdan subgroups of nV for n ≥ 2 stays open. It is the
    sharp crux shared with Problem 2.7.
- 2026-09-13, same lane: properties of nV that pass to subgroups but do not
  obstruct hyperbolic groups are solvable word problem, torsion local finiteness
  (claimed by Kojima–Sheng, arXiv:2603.18410, for all `n`; for `n >= 2` the proof is
  invalid, `kojima-sheng-two-generator-torsion-criterion-fails-in-v` (a22c90a4a), so
  this property is itself open, `brin-thompson-2v-is-torsion-locally-finite`, `brin-thompson-groups-contain-infinite-periodic-groups`) and
  abelian germ groups of point stabilizers.
