---
rg: 2
id: v-times-shift-alternating-group-is-of-type-fp2
kind: claim
title: "The alternating full group of V times the full two-sided shift is of type FP_2"
---

With the notation of `v-times-shift-alternating-group-restrictions-are-simple`,
the group `A(G)` for `G = G_V × (Z ⋉ {0,1}^Z)` is of type FP_2 over `Z`.
Finite presentability would be stronger than needed.

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2): `A(G)` is finitely generated
  (Nekrashevych, arXiv:1511.08241: expansive groupoids). It contains
  - copies of `V` controlled by clopen sets of the shift coordinate, conjugated
    around by the shift;
  - shifts controlled by cylinders of `C`;
  - the abelian group `C(C, Z)` of controlled shift exponents, normalized by `V`.
- It is a subgroup of the Brin–Thompson group `3V`. Split
  `{0,1}^Z = {0,1}^N × {0,1}^N` into past and future. The shift then becomes
  the baker's map `(p, f_0 f') ↦ (f_0 p, f')`, an element of `2V`. So `G` is an
  open subgroupoid of the groupoid of `3V`, and `[[G]] ≤ 3V`.
- No finiteness proof is known. A Stein–Farley-type complex for the germs of
  `G` (prefix trees in the `C` coordinate, clopen partitions with shift labels
  in the `Σ` coordinate) with Brown's homological criterion is the natural
  attempt. The needed input is homological 1-connectivity of descending links
  over a Z-labelled partition complex, which has not been checked.
- Dies if: some quotient or retract of `A(G)` is visibly not FP_2, for example a
  lamplighter-like `C(Σ, V) ⋊ Z` retract. None has been found; restricting to a
  periodic orbit gives Higman–Thompson-type quotients, which are of type F_∞.
- 2026-09-17 (swarm-0917-w4-z-fp2-countable, symbolic-dynamics), **two established
  results, node still OPEN.**
  - **The Stein–Farley attempt above dies at cocompactness.** An ample groupoid
    with `m` similarity types of basic clopens has at most `m` minimal closed
    invariant sets (`finite-similarity-types-bound-minimal-invariant-sets`).
    `G` has `2^aleph_0` of them, so it has no finite type system
    (`v-times-shift-groupoid-has-no-finite-similarity-types`). Heuristically
    the types are indexed by all tape words `w`. So the filtration by the number of
    pieces is never cocompact. The same holds for every ambient groupoid that
    can feed `uncountably-many-simple-fp2-via-v-times-shift-restrictions`. A
    surviving proof needs a two-parameter filtration (number of pieces, maximal
    word length) and connectivity across increasing word length.
  - **Necessary conditions that can fail on their own.** The kernels proof
    covers every closed invariant `Y`, so FP_2 of `A(G)` forces FP_2 of
    `A(G|_{C×Y})` for all subshifts `Y`
    (`v-times-shift-fp2-forces-fp2-of-every-subshift-restriction`).
  - **Correction to the previous bullet.** The fixed point `0^Z` gives
    `C(C, Z) ⋊ V`, not a Higman–Thompson group: the isotropy `Z` survives as
    controlled shift exponents. Its FP_2 status is the cheapest open test.
  - Where it stops: no obstruction and no proof. It is not checked whether
    `C(C, Z) ⋊ V` is FP_2, and descending links for the two-parameter filtration
    were not attempted.
- 2026-09-18 (swarm-0917-w6b-w6b-re-pull-z-3, reframing), **the fixed-point test
  passes, node still OPEN.**
  - `C(C, Z) ⋊ V` is the one-point abstract twisted Brin–Thompson group
    `{s}V_Z`. The trivial action `Z ↷ {s}` is of type [A_2], so FFWZ Theorem
    4.1(ii) makes it finitely presented
    (`cantor-integer-maps-by-v-are-of-type-fp2`).
  - So item 2 of `v-times-shift-fp2-forces-fp2-of-every-subshift-restriction`
    holds, and the cheapest open test named above cannot kill the route. Any
    obstruction must come from the shift dynamics, meaning infinite subshifts or
    `Σ` itself.
  - Where it stops: periodic orbits of period `n ≥ 2` were not checked, and no
    finiteness proof for `A(G)` was attempted.
