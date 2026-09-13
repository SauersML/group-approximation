---
rg: 2
id: wreath-z-by-z2-embeds-in-thompson-v
kind: claim
title: The wreath product of Z by Z^2 is isomorphic to a subgroup of Thompson's group V
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md
---

`Z ≀ Z^2` is isomorphic to a subgroup of Thompson's group `V`.

With `wreath-z-by-z2-does-not-embed-in-thompson-f`, this would answer the reposed Problem
2.15 negatively: `Z ≀ Z^2` is bi-orderable and metabelian.

## Attempts

- 2026-09-13 (z2-15b-biorderable). Artifact part 3, §"Z ≀ Z^2 inside V".
  - *Dead: wandering lamps.* A lamp supported on a clopen set whose `Q`-translates are
    pairwise disjoint is impossible. Commuting `s, t` on a common flow component have a
    nonzero combination acting trivially there (needs the structure input V0+).
  - *Dead: two-cone models.* With `s` and `t` flowing on disjoint cones, cone-preserving
    lamps satisfy `(1 − x^s)(1 − x^t)·a = 1`. Cone-swapping lamps fail to commute with
    their `t`-conjugates.
  - *Open.* A construction must use lamps whose supports overlap without the
    equal-or-disjoint bump structure of `F`. A disproof must find `Q`-invariant,
    base-invariant pieces on which a nonzero stabilizer fixes the restricted lamp, as in
    part 2.
  - *Tool.* Bodart–D'Angeli–Perego–Rodaro (arXiv:2608.02111): a f.g. group embeds in `V`
    iff it has a faithful context-free action. Deciding whether `Z ≀ Z^2` has one is an
    equivalent formulation.
