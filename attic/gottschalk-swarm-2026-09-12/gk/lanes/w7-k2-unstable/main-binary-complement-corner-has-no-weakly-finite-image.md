---
rg: 2
id: binary-complement-corner-has-no-weakly-finite-image
kind: claim
title: The binary complement corner of the Leavitt unit group algebra has no nonzero weakly finite image
refuted_by:
  - binary-leavitt-units-carry-nonaugmentation-rank-function
distinct_from:
  ternary-anti-central-summand-has-no-weakly-finite-image: that is the ternary form on the anti-central summand eps_- F_3[G_3], where a central character splits off the augmentation; this is the binary form on the non-central corner (1 - e) F_2[R^x] (1 - e), where no character splits it off.
  binary-complement-corner-states-give-sylvester-rank-functions: that is the open state-to-rank-function step U1 on T; this is equivalent to the full corner outright, with no states and no rank functions.
artifacts:
  - research/artifacts/binary-weakly-finite-representations-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, with `g`, `e = 1 + [g] + [g²]` and `f = 1 - e` as
in `binary-cyclic-corner-full-iff-complement-corner-has-no-state`, and put `T = f A f`. Then every nonzero
quotient ring of `T` contains a square matrix with a one-sided inverse that is not invertible.

**It is the binary counterexample.** By `rank-condition-rings-have-weakly-finite-images` and
`binary-cyclic-corner-full-iff-complement-corner-has-no-state`, this claim is equivalent to
`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` (route
`binary-cyclic-corner-from-no-weakly-finite-complement-image`). That gives Kaplansky failure for `G`, and
the landed chain continues to the goal.

**Equivalent representation form** (`binary-corner-weakly-finite-images-are-unit-representations`): every
group homomorphism from `L_(F_2)(1,2)^x` into the unit group of a weakly finite ring of characteristic two
is trivial. The statement no longer mentions `g`.

**Refuted by:**
- any non-augmentation Sylvester rank function on `F_2[G]`, since its null quotient is weakly finite;
- any `F_2`-linear sofic approximation of `G`;
- any nontrivial homomorphism from `G` into the units of a stably finite ring of characteristic two.

## Attempts

- 2026-09-12 `w5-wf-binary`: opened as the rank-free form of the binary corner (artifact Theorem W).
  - **Dead targets.** Division rings of characteristic two are ruled out by an elementary argument
    (`C_3² <= G` cannot sit in a finite field). So are matrices over them (complement-corner artifact,
    Corollary 4.2) and commutative rings (`G` is perfect).
  - **Evaluation.** The evaluation quotient `π(f) R π(f)` is purely infinite, so it is not weakly finite, and
    a weakly finite image has to be nonzero on `f (ker π) f`.
  - **What a proof needs.** From unit relations of `G` alone, produce square matrices `X, Y` over any quotient
    `W` of `T` with `XY = I`. Leavitt isometries are not group elements, so they are available only through
    units such as `D(h)`, the permutation units and the halving map `ψ'`.
  - **Firewalls.** Every sofic, locally finite, HNN or Fock data set on main carries a rank model, hence a
    weakly finite image. So the relations used must involve overlapping supports or a nonsofic subgroup
    containing `g`.
  - **No mechanism yet.**
- 2026-09-12 `w6-mismatch-c2`: depth-mismatched transvection factors. Firewall, no mechanism.
  - **The pair.** The lever pair `T_(0,1)`, `T_(1,00)`, whose product has infinite order, lies in the tree
    `R_0^x - H - g^-1 R_0^x g` of locally finite subgroups, where `H` is block-triangular.
  - **Weakly finite model.** `graphs-of-locally-finite-groups-carry-regular-rank-models` gives a nontrivial weakly
    finite representation of that tree's fundamental group, nonzero on the two-root defect. So those relations cannot
    rule out a weakly finite image.
  - **Broken relation.** The single-letter HNN extension breaks `[T_(01,00), T_(1,00)] = 1`, and `H` repairs it.
  - **What a proof must use.** One of: a nonsofic cycle of Steinberg relations through the pair, `K_2(3,R)`, or a
    global input.

    Artifact `research/artifacts/mismatched-factor-graph-of-groups-firewall-2026-09-12.md`.
