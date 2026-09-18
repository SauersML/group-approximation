---
rg: 2
id: some-gl-n-z-embeds-in-no-brin-thompson-group
kind: claim
title: Some GL_n(Z) embeds in no Brin-Thompson group mV
distinct_from:
  every-gl-n-z-embeds-in-some-brin-thompson-group: that is the affirmative answer to Zaremsky 2.19(c); this is its negation.
  zaremsky-2-19c-every-gl-n-z-in-some-mv-resolved: that claim is Zaremsky's question 2.19(c); this claim is its negative answer.
---

**OPEN.** Every route into this claim is conditional on an open claim:
- `some-gl-n-z-in-no-nv-via-kazhdan-finiteness` needs `kazhdan-subgroups-of-brin-thompson-groups-are-finite`,
  which is open for `n ≥ 2`;
- `some-gl-n-z-in-no-nv-via-heisenberg` needs `heisenberg-group-embeds-in-no-brin-thompson-group`, of which
  only `m = 1` is established;
- `gl-3-z-in-no-nv-via-cnd-transversal` needs `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`, which is
  open.

The negation `every-gl-n-z-embeds-in-some-brin-thompson-group` is also open.

There is `n` such that for every `m >= 1`, `GL_n(Z)` is not isomorphic to any
subgroup of `mV`. Necessarily `n >= 3`, since `GL_2(Z)` embeds in `V`.

**Routes into this claim.**
- `some-gl-n-z-in-no-nv-via-kazhdan-finiteness`: from finiteness of all Kazhdan
  subgroups of all `nV` (`kazhdan-subgroups-of-brin-thompson-groups-are-finite`),
  since `SL_3(Z) = EL_3(Z)` is infinite with property (T).
- `some-gl-n-z-in-no-nv-via-heisenberg`: from
  `heisenberg-group-embeds-in-no-brin-thompson-group`.

## Attempts

- 2026-09-13 (lane z2-19-glnz-q-2v, unreviewed): **the undistortion route is
  dead for m >= 2.**
  - For `V`, undistortion of cyclic subgroups excludes `H_3(Z)`
    (`thompson-v-has-no-heisenberg-subgroup`), and with it every `GL_n(Z)`,
    `n >= 3`.
  - The drift version holds in every `nV`: an element with a drifting invariant
    measure is undistorted (`heisenberg-in-nv-forces-drift-free-central-element`,
    item 1).
  - But `mV` with `m >= 2` contains a distortion element with `|f^N| = O(log^4 N)`
    (`brin-thompson-mv-contains-a-distortion-element`). So "no infinite-order
    element is drift-free" is false there, and a negative answer needs an
    obstruction other than distortion of cyclic subgroups.
- 2026-09-13, same lane: **candidate obstructions still open.**
  - The Haagerup property of `nV`, or finiteness of its Kazhdan subgroups
    (Problem 2.7). Cube-complex proofs are excluded for `m >= 2` (Callard–Salo,
    Corollary 1.2).
  - A finer use of the offset cocycle. For a Heisenberg triple `a, b, c = [a,b]`
    in `mV`, the drift of `c` vanishes for every invariant measure, and for
    `ab`-invariant measures the commutator relation forces more rigid
    cancellation of offsets along orbits. No contradiction was found.
  - Algebraic obstructions from subgroups of `GL_n(Z)` that `mV` might omit. The
    Belk–Bleak–Matucci conjecture (arXiv:1602.08635, Conjecture 1.7) predicts
    that `Z^(m+1) * Z` is not in `mV`. All RAAGs embed in some `GL_N(Z)`
    (right-angled Coxeter groups are integral linear via the Tits
    representation, and RAAGs embed in them by Davis–Januszkiewicz; not
    re-read). Even if true, this excludes large `GL_N(Z)` from each fixed `mV`,
    which answers 2.19(d) but not 2.19(c).
