---
rg: 2
id: f-infinity-without-finite-vcd-non-proper-bnsr-inclusion
kind: claim
title: "Every group G of type F_infinity with no finite-index subgroup of finite cohomological dimension has some m >= 1 with Sigma^m(G) = Sigma^{m+1}(G)"
distinct_from:
  non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion: that claim quantifies over all F_infinity groups with no finite classifying space; this one only over F_infinity groups with no finite-index subgroup of finite cohomological dimension, the part left open by virtually-finite-cd-f-infinity-groups-have-stable-bnsr
  every-f-infinity-group-has-a-non-proper-bnsr-inclusion: that claim quantifies over all F_infinity groups; this is its remaining open case
---

Let `G` be a group of type `F_∞` such that every subgroup of finite index in
`G` has infinite cohomological dimension. Then there is `m ≥ 1` with
`Σ^m(G) = Σ^{m+1}(G)`.

- **Relation to the negative answer to 1.18.** With
  `virtually-finite-cd-f-infinity-groups-have-stable-bnsr` this gives
  `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`, and so the
  negative answer to Zaremsky Problem 1.18. See route
  `non-type-f-non-proper-bnsr-by-virtual-cd-dichotomy`.
- **The affirmative answer lives here.** Any group answering 1.18
  affirmatively lies in this class, and so does every finite-index subgroup of
  it (`bnsr-invariants-are-detected-on-finite-index-subgroups`).

## Attempts

- 2026-09-16 (swarm lane on Problem 1.18). **What is already covered inside
  this class.**
  - Groups with finite abelianization, where `S(G)` is empty.
  - Groups with the Bieri Σ-property
    (`bieri-sigma-property-forces-bnsr-constant-from-rank`).
  - Groups acting properly and cocompactly on a contractible
    finite-dimensional complex
    (`cocompact-contractible-d-complex-bnsr-stabilize-at-d`).
  - Groups with a finite-index subgroup from any of these classes. The chain
    stabilizes upward through restriction
    (`bnsr-invariants-are-detected-on-finite-index-subgroups`).
- **Members with computed invariants stop at level 2.**
  - Thompson's group `F` is in the class. Elements supported on `n` disjoint
    intervals give `Z^n ≤ F`. A finite-index subgroup `H` meets it in a
    finite-index subgroup of `Z^n`, again free abelian of rank `n`, so
    `cd H ≥ n` for every `n`.
  - For `F` and the other computed Thompson-like groups (`F_{n,∞}`, `F_{2,3}`,
    the Lodha–Moore groups), the invariants stop at level 2. Sources are listed
    in `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`.
- **Where each available tool dies.**
  - *Dimension arguments.* The Novikov-homology argument behind
    `bnsr-invariants-stabilize-at-cohomological-dimension` needs
    `Tor_i^{ZH}(\widehat{ZH}_{-χ}, Z) = 0` for all large `i`, for some
    finite-index `H`. As written, it gets this from `cd H < ∞`, which fails
    for every finite-index subgroup of a group in this class. A vanishing
    range for the Novikov coefficients alone would be weaker, but no source for
    it is known here.
  - *Cocompact Σ^m-criterion.* The argument behind
    `cocompact-contractible-d-complex-bnsr-stabilize-at-d` needs a
    finite-dimensional model. Thompson-like groups act on infinite-dimensional
    Stein–Farley complexes.
  - *Finite index.* This cannot help in either direction: a counterexample
    restricts to counterexamples, and passing to finite index leaves the class
    unchanged.
  - *Elementary amenability.* All elementary amenable groups of type `F_∞` are
    excluded (`elementary-amenable-f-infinity-groups-are-type-vf`).
  - *Kropholler's class LH𝔉.* The finiteness theorem for LH𝔉 groups of type
    `FP_∞` (Kropholler, J. Pure Appl. Algebra 90 (1993) 55–67) would exclude
    much more. Its exact statement was not verified here.
    Januszkiewicz–Kropholler–Leary, arXiv:0908.3669v1, §1, say only that `F`
    is of type `FP_∞` "and yet having infinite cohomological dimension and so
    failing the key finiteness theorem for HF-groups of type FP∞ established in
    [k-fpinfty]". If the
    theorem is the paraphrase recorded in
    `every-torsion-free-f-infinity-group-of-infinite-cd-contains-f` ("torsion-free
    LH𝔉 groups of type FP_∞ have finite cd"), then the torsion-free members of
    this class lie outside LH𝔉.
- **What a proof would need.** A bound on the number of distinct levels from
  data other than dimension. Candidates:
  - the size-bounded Morse principle for Stein–Farley-type complexes with
    finitely many move types (heuristic, part 2 §3 of
    `research/artifacts/zp-properly-nested-bnsr-2026-09-13-part2.md`);
  - a product or extension formula controlling levels through a normal
    subgroup of finite cohomological dimension.
