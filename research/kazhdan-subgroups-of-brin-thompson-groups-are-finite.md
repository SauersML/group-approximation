---
rg: 2
id: kazhdan-subgroups-of-brin-thompson-groups-are-finite
kind: claim
title: For every n, every subgroup of the Brin-Thompson group nV with property (T) is finite
distinct_from:
  thompson-v-has-haagerup-property: that is Farley's theorem for V = 1V, which gives this finiteness for n = 1 through a proper action; this asks for the finiteness for every n, where no proper action and no commensurated subset are known.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that treats Rover-Nekrashevych groups over one tree, where a commensurated set of cones exists; this treats the product Cantor cubes of nV, where subcubes are not commensurated.
  some-hyperbolic-group-embeds-in-no-brin-thompson-group: that is the negative answer to Zaremsky 2.19(a), which this claim implies but which could also come from another obstruction; this is the finiteness of all Kazhdan subgroups of all nV.
---

For every `n ≥ 1` and every subgroup `K ≤ nV` with property (T), `K` is finite.

## Status

- **n = 1.** Established (`thompson-v-has-haagerup-property`). Also, FW subgroups
  of V are finite (`fw-subgroups-of-eventually-similar-groups-virtually-embed`,
  case of canonical similarities).
- **n ≥ 2.** Open.

## What it would give

- Zaremsky Problem 2.19(a) has answer no. No infinite hyperbolic Kazhdan group
  embeds in any nV (route `some-hyperbolic-group-in-no-nv-via-kazhdan-finiteness`).
- Zaremsky 2.19(c) and 2.19(d) have answer no, because SL_3(Z) has property (T).
- No nV has property (T), which settles the (T) half of Zaremsky Problem 2.7
  (`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`) negatively. It does not
  settle the Haagerup half.
- The claim follows from the Haagerup property of nV for infinitely many n,
  since jV embeds in kV for j < k. It is weaker than that property.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv, unreviewed): **commensurated subcubes
  fail for n ≥ 2.**
  - The V proof commensurates the set of cones. For nV the set of subcubes is not
    commensurated.
  - Let `C = {0,1}^ω`. The rearrangement of `C^2` fixing `C×[0]` and swapping
    `[0]×[1]` with `[1]×[1]` by changing the first digit of coordinate 1 sends
    `[w]×C` to `[w]×[0] ∪ [w']×[1]` with `w' ≠ w`, which is not a subcube, for
    every nonempty prefix `w`.
  - Restricting to diagonal or fat subcubes removes the broken ones but not the
    problem. An element with prefix-length change vector `s` on a piece changes
    the shape by `s`, so every family defined by a shape condition has infinite
    symmetric difference with its image once `s` is not constant.
- 2026-09-13, same lane, unreviewed: **orbit isoperimetry gives nothing.**
  - Orbits of nV on `C^n` carry the prefix-replacement metric, and elements act
    with bounded displacement.
  - Such orbits are coarsely products of trees, so they are non-amenable, and a
    Kazhdan group acting with non-amenable Schreier graphs is not excluded.
  - Contrast: inside 2V the baker's map `(0x, y) ↦ (x, 0y)`, `(1x, y) ↦ (x, 1y)`
    is conjugate to the two-sided full shift, so the topological full group of
    the full shift embeds in 2V.
  - Its orbits are copies of Z, so a finitely generated Kazhdan subgroup `K`
    acts on each orbit with displacement bounded by a constant `r`. Infinite
    orbits are amenable Schreier graphs, so all orbits are finite.
  - On a finite orbit of size `N`, the Schreier graph has bandwidth at most `r`,
    so it has a balanced cut with at most `O(r^2)` edges. The Kazhdan spectral
    gap then bounds `N`.
  - Uniformly bounded orbits give finitely many finite quotients, so `K` is
    finite.
  - So that subgroup of 2V contains no infinite Kazhdan group. The argument uses
    amenable orbits and does not extend to nV.
- 2026-09-13, same lane: **proper cubical actions are excluded for n ≥ 2.**
  - Callard–Salo (arXiv:2208.00685, Corollary 1.2) and Kojima–Sheng
    (arXiv:2603.18410, Corollary 4.3) state that mV has no proper action on a
    CAT(0) cube complex for m ≥ 2. Both are imported in
    `brin-thompson-mv-contains-a-distortion-element`.
  - So Farley's route for V (a proper cubical action, then the Haagerup
    property, then finite Kazhdan subgroups) cannot work verbatim.
  - Two routes remain (unreviewed):
    - A commensurated subset of an nV-set gives an action on a CAT(0) cube
      complex (Sageev), and every subgroup with property (T) fixes a vertex of
      it. Finiteness then needs only that every Kazhdan subgroup of every vertex
      stabilizer is finite, not properness. The V case has this shape
      (`fw-subgroups-of-eventually-similar-groups-virtually-embed`).
    - A proper affine isometric action on Hilbert space that is not cubical.
      Distortion does not forbid one: BS(1,2) is amenable, so a-T-menable, and
      contains a distortion element.
- Next target: find an nV-set with a commensurated subset whose vertex
  stabilizers have only finite Kazhdan subgroups, or build an infinite Kazhdan
  subgroup of 2V. Abstract twisted Brin–Thompson groups have property FW_∞
  (Fournier-Facio–Wu–Zaremsky, arXiv:2603.24687). This lane has not checked what
  that property excludes for classical nV.
