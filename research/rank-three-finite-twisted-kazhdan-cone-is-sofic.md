---
rg: 2
id: rank-three-finite-twisted-kazhdan-cone-is-sofic
kind: claim
title: The rank-three finite twisted Kazhdan cone, twisted by evaluation at the origin, is sofic
distinct_from:
  finite-twisted-kazhdan-cone-is-sofic: that asks the question for every rank r ≥ 3 and is refuted for r ≥ 5 by block subpairs; this is the rank-three case, where no 3-element block has a disjoint centralising element.
  block-subpairs-make-twisted-kazhdan-cones-nonsofic: that proves nonsoficity whenever a block subpair has a trace with nontrivial centraliser; this is the case where every block trace is all of Gamma.
---

**OPEN.**  Let `R_+ = F_q[x_1..x_d]` and `R = F_q[x_1^(±1)..x_d^(±1)]` with `d ≥ 3`.  Let
`Gamma = EL_3(R_+) ≤ G = EL_3(R) x| SL_d(Z)` be the rank-three Kun-Thom Theorem E pair.  Let
`psi : Gamma -> F = PSL_3(F_q)` be evaluation at the origin followed by projection.  Is

```text
T_3 = (F x Gamma) *_(Gamma_psi) G
```

sofic, for some prime power `q` and some `d ≥ 3`?  The companion case `r = 4`, `q ∈ {2, 3, 5}` of
[[finite-twisted-kazhdan-cone-is-sofic]] is equally open and would serve the same purpose.

**Why it matters.**  By [[block-subpairs-make-twisted-kazhdan-cones-nonsofic]], every twisted-diagonal cone
over a Theorem E pair of rank `r ≥ 5` is nonsofic, for every twist.  The same holds in rank four for
`q ∉ {2, 3, 5}`.  So the twisted-cone route of [[kazhdan-double-cones-add-one-sigma1-bit]] to
[[sofic-recognition-finite-presentations-is-pi2-complete]] survives only through these low-rank pairs.  By
[[twisted-diagonal-cones-need-a-profinitely-invisible-core]] it survives only through a twist with a
centreless invisible core, and `T_3` is the basic example.

**What is known.**
- `T_3` is not residually finite.
- Every finite-index level `G_1` has `psi(Gamma ∩ G_1) = F`, by (V5) of the invisible-core node.
- The only block subpair is `(G, Gamma)` itself, and `F` is centreless.

**What would decide it.**
- *Nonsofic.*  Find a subgroup `B ≤ G` with `C_F(psi(B ∩ Gamma)) ≠ 1` and `B *_(B ∩ Gamma) B` nonsofic.  Such a
  `B` must have infinite index and must not be normal.  If `B ∩ Gamma` has finite index in `Gamma`, for instance
  `ker ev_0`, then `B` must avoid most of the nonnegative compressors in `SL_d(Z)`, because `ker ev_0` and
  `SL_d(Z)` together generate `G`.  Relative groups `EL_3(R, I) x| Stab(I)` over ideals `I` vanishing at the
  origin are the candidates named in [[finite-twisted-kazhdan-cone-is-sofic]].
- *Sofic.*  Build sofic approximations of `T_3`.  They cannot come from finite quotients of `T_3`.  This would be the first soficity theorem for an
  amalgam over a Kun-Thom subgroup that is not a free factor.

## Attempts

- **w8-111r, 2026-09-18: hypersurface-level subpairs (obstruction).**
  - *Result.*  By [[divisor-level-subpairs-cannot-certify-rank-three-twisted-cone]], graded diagonal twists
    `B = D (EL_3(F_q[L]) x| H) D^-1` satisfy the centraliser condition.  Their origin image lies in the torus, and
    `B` is Kazhdan with `B ∩ Gamma` infranormal and not normal in `B`.  But `B ∩ Gamma` maps onto an infinite
    Borel subgroup over `F_q[x_2..x_d]`, so it is not Kazhdan.  The relative groups `EL_3(R, I) x| Stab(I)` fail
    too, for every ideal `I`: either `psi(B ∩ Gamma) = F`, or `B ∩ Gamma` has an infinite abelian quotient.
  - *Why.*  Both families shrink `psi(B ∩ Gamma)` by a level along a hypersurface, and that level becomes an
    infinite amenable quotient of the edge.
  - *What is left.*  A Kazhdan edge with a level only at the origin, such as `ker ev_0` or `ev_0^-1(Borel)`,
    inside a subgroup `B` that avoids the nonnegative compressors.  Or build sofic approximations.
  - *Graph.*  This node now feeds the route [[sofic-fp-completeness-from-rank-three-twisted-kazhdan-cones]].
