---
rg: 2
id: sl3-laurent-f2-is-flexibly-hs-stable
kind: claim
title: SL_3(F_2[t,1/t]) is flexibly Hilbert--Schmidt stable
distinct_from:
  el-r-polynomial-vertex-not-flexibly-hs-stable: that concerns instability of the polynomial vertex SL_3(F_q[t]) and EL_3(F_q[x]), using that they are infinitely presented; this is stability of the Laurent host SL_3(F_2[t,1/t]) that contains the vertex as a co-dense subgroup
  stable-group-with-codense-kazhdan-subgroup: that asks for any stable host with a co-dense Kazhdan subgroup; this names one candidate whose Kazhdan and co-density hypotheses are proved
---

**OPEN.**  `A=SL_3(F_2[t,1/t])` is flexibly Hilbert--Schmidt stable, in the
sense consumed by the corollary of
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` (Dogon--Vigdorovich's
flexible notion).

Consequences, through the routes below:
- `<A,s | [s,SL_3(F_2[t])]=1>` is non-hyperlinear;
- `L(SL_3(F_2[t])) subset L(A)` is not `RE/C`;
- the Kun--Thom double at `(q,r)=(2,3)` is non-hyperlinear for every `d>=3`,
  and so is the opposite-slice double.

## Attempts

- **Strict stability is excluded.**  `A` is residually finite and Kazhdan
  (`elementary-groups-over-fg-rings-have-property-t`).  By the graph's node
  `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, same-dimension
  stability fails.  Only the flexible form is open.
- **Vertex instability does not transfer.**  The route
  `el-r-vertex-instability-via-rank-three-covers` looks for non-roundable
  models of the infinitely presented vertex `SL_3(F_q[t])`.  Such models are
  not models of `A`, and restricting a model of `A` to the vertex does not
  produce them.
- **Number-field analogue.**  The same statement for `SL_3(Z[1/2])` feeds
  `non-hyperlinear-from-hnn-over-sln-z` and is open.  No tool specific to
  characteristic `p` is known to help.  The torus recurrence proving
  co-density is exact and says nothing about approximate models.
- **Cohomological instability is void on the whole commensurability class
  (2026-09-13, lane ex2-hecke-pair-negative).**
  - By Harder (`harder-function-field-s-arithmetic-cohomology-vanishing`),
    every congruence subgroup of `A` has rational cohomology only in degrees
    0 and 4.
  - `laurent-sl3-real-cohomology-from-chamber-quotient`: `A(f)` acts on the
    `t`-adic building with one chamber as quotient. None of the real `H^2`
    classes of the one-place vertex groups (927 at level `t^2+1`) extends
    compatibly across the three edge groups.
  - `laurent-sl3-central-covers-never-witness-instability`: at every subgroup
    containing a congruence subgroup, central Kazhdan covers have finite
    kernel, so their pulled-back models round strictly. Asymptotically
    projective models also round strictly.
  - So neither Ioana--Spaas--Wiersma Theorem A nor Dogon's Theorem 1.3, the
    mechanism of `rf-kazhdan-group-not-flexibly-hs-stable`, has input here.
    `A` is finitely presented (Bux--Köhl--Witzel rank theorem, local ranks
    `2+2`), so the infinitely-presented corollary of
    `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` does not apply
    either.
  - A witness of instability needs genuinely non-scalar defects. The
    remaining shape is a non-central Kazhdan cover whose kernel admits
    almost-trivial representations without fixed vectors.
  - If the kernel `N` is abelian, the trace of such a model gives
    `A`-invariant probability measures on the dual of `N` that concentrate at
    the trivial character without an atom there. This is excluded when the
    conjugation action on `N` has finite image, which reduces to the central
    case, and when `(N ⋊ A, N)` has relative property (T).
  - What is left is modules with infinite orbits and no relative (T), such as
    permutation modules on the vertex set `A/SL_3(F_2[t])` of the building.
    That is the coset-wreath shape of the positive polarity
    (`function-field-hecke-pair-is-relatively-embeddable`). The last two
    bullets are a sketch, not an established node.
- **What (T), the congruence subgroup property and character rigidity buy
  (sketch, 2026-09-13).**
  - Let `α` be the tracial ultraproduct of a model. For each congruence
    subgroup `A(g)`, the Kazhdan projection of `A(g)` is central in `C*(A)`,
    so its image `P_g` is central in `α(A)''`. On `P_g`, `α` factors through
    the finite group `A/A(g)`, and that corner rounds strictly because finite
    groups are HS-stable.
  - The complementary corner has no congruence-invariant mass. Suppose every
    extreme character of `A` is `δ_e` or finite-dimensional (character
    rigidity; not verified for this group in the graph). Then that corner has
    limit character `δ_e`. So flexible stability of `A` reduces to models
    with limit character `δ_e`.
  - In the `δ_e` regime, co-density with trivial coefficients is automatic:
    for a Kazhdan subgroup `H` of infinite index, `α(p_H) = 0 = α(p_A)`.
  - The one rounding obstruction left is adjoint. Item 3 of
    `function-field-hecke-pair-is-perfect-codense-kazhdan` makes every
    almost `SL_3(F_2[t])`-central unitary of a roundable model almost commute
    with the torus element `h`.
  - A `δ_e` model violating this is a microstate of the centralizer HNN group
    with `[s,h]` bounded away from 1, which is the positive polarity. So these
    three tools cannot settle the problem without also settling that
    microstate question.
