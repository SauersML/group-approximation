---
rg: 2
id: thompson-f-admits-a-faithful-2-transitive-action
kind: claim
title: Thompson's group F admits a faithful 2-transitive action
---

There is a set `Ω` with `|Ω| ≥ 3` and a faithful action of Thompson's group `F`
on `Ω` that is transitive on ordered pairs of distinct points. Equivalently,
there is a core-free subgroup `H < F` with exactly two `(H,H)`-double cosets,
`F = H ⊔ HgH`. Together with `thompson-f-transitivity-degree-at-most-two`,
this would give `td(F) = 2`.

## Attempts

- 2026-09-13 (z2-20-f-2-transitive). Necessary conditions on `H`, all
  unreviewed:
  - maximal of infinite index;
  - containing no `F_U^c`
    (`thompson-f-two-transitive-rigid-stabilizers-fix-no-point`);
  - minimal on `(0,1)` and not confined
    (`thompson-f-two-transitive-stabilizers-minimal-not-confined`).
  Closedness and the Le Boudec–Matte Bon grid condition come for free for
  maximal subgroups of infinite index (Golan, arXiv:2209.03244), so they do not
  narrow the search.
- Candidates: stabilizers `Stab_F(S)` of dense, codense sets `S` of dyadic
  fractions; stabilizers of colorings of the dyadic fractions (closed maximal
  subgroups are determined by germs); the explicit non-parabolic maximal
  subgroups of Golan–Sapir (arXiv:1508.00493, the preimage of Jones' subgroup
  under an injective endomorphism, Theorem 3.15) and Golan's infinite family
  (arXiv:2209.03244).
- **Test protocol** for an action on translates of a set `S`, i.e.
  `H = Stab_F(S)`, with `Δ = S Δ gS`:
  - (T1) if some `g` makes `min Δ` or `max Δ` exist, the relation "the extreme
    point lies in the second set only" is invariant and antisymmetric, so the
    action is not 2-transitive;
  - (T2) otherwise, at `t0 = inf Δ` both `S \ gS` and `gS \ S` must accumulate
    at `t0` from the right. Otherwise one-sided inclusion near `t0` is an
    antisymmetric invariant;
  - (T3) for colorings with at least 3 colors, the ordered color pair at an
    extreme disagreement point is an antisymmetric invariant.
  The same tests apply to any closed `H`, replacing `S` by its germ groupoid.
  Not yet run on a concrete maximal candidate: the difficulty is that dense
  self-similar sets such as the odd digit sum dyadics make `Δ` accumulate at
  its extreme points.
