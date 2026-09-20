---
rg: 2
id: thompson-t-mf-iff-finite-quotient-corners
kind: claim
title: "T is MF iff finite quotients of Z/4 * Z/3 carry almost-invariant corners with small compressed T-defect and nontrivial compressed generators; every such corner in a finite group F has level at least 1/(18 diam F)"
distinct_from:
  thompson-t-padded-cover-stability-is-inert: that measures the absolute defect of the padded representation pi, which is the maximum over the blocks and so is decided by the auxiliary block; this measures the compressed (relative) defect on the almost-invariant corner cut out by the original block, where the padding is invisible, and it gives an equivalence with MF rather than a kill.
  torus-knot-groups-are-rq-stable: that is Willett's R_q-stability of K(3,4), an input here; this converts it, together with a central retwist, into a finitary characterisation of MF for T in which the auxiliary block is removed by compression.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that characterises MF by exact pairs of arbitrary infinite-image type; this shows the witnesses can always be taken as compressions of representations of finite groups, and conversely.
  thompson-t-triangle-genuine-rep-relator-gap: that records that whole finite-quotient representations have defect at least 1/2; this shows that their almost-invariant corners are nevertheless complete for the MF question.
  lie-closure-trichotomy-without-finite-quotients: that is the structure theorem whose item 2 gives the 1/2 bound for finite images; this uses that bound only to prove the diameter item.
  thompson-t-near-pairs-round-to-triangle-reps: that is trivially padded rounding onto honest Delta(4,3,5)-representations; this uses arbitrary finite-image padding and no rounding of the corner onto an honest representation.
artifacts:
  - research/thompson-t-mf-iff-finite-quotient-corners-proof.md
---

**ESTABLISHED** by `thompson-t-mf-iff-finite-quotient-corners-proof` (written proof, unreviewed). The
inputs are `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, `torus-knot-groups-are-rq-stable` (a
literature import from Willett, arXiv:2408.13350) and item 2 of
`lie-closure-trichotomy-without-finite-quotients`.

## Setting

Use the notation of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`:
`G0 = Z/4 * Z/3 = <a, b | a^4, b^3>`, and `T = G0 / <<r_1, r_2, r_P>>` with `r_P = (ba)^5`. A **finite
quotient** of `G0` is a finite group `F` with a chosen generating pair, also written `a, b`, such that
`a^4 = b^3 = 1` in `F`. Write `diam F` for the diameter of its Cayley graph with respect to
`{a^(+-1), b^(+-1)}`.

Let `pi` be a unitary representation of `F` on a finite-dimensional space, and `P != 0` a projection. The
triple `(F, pi, P)` is an **eps-corner** if

```text
(C1)  ||[P, pi(a)]|| < eps   and   ||[P, pi(b)]|| < eps                       (almost invariant)
(C2)  ||P (pi(r) - 1) P|| < eps       for r = r_1, r_2, r_P                    (small compressed defect)
(C3)  ||P (pi(a) - 1) P|| >= 1   or   ||P (pi(b) - 1) P|| >= 1                  (nontrivial compression)
```

All norms are operator norms. The corner level of `F` is
`c(F) = inf { eps : F carries an eps-corner }`, with `inf {} = +infinity`.

## Statement

**Theorem A (finitary form of MF).** The following are equivalent.
1. `T` is MF, that is, `T` does not have full MF radical.
2. For every `eps > 0` some finite quotient `F` of `G0` carries an `eps`-corner, i.e. `inf_F c(F) = 0`.
3. The same holds with `pi` a multiple of the left regular representation of `F`.

Equivalently, `thompson-t-has-full-mf-radical` holds iff `inf_F c(F) > 0`, the infimum being taken over
all finite quotients of `Z/4 * Z/3`.

**Theorem B (diameter bound).** Every finite quotient `F` of `G0` has

```text
c(F) >= 1 / (18 diam F).
```

So a sequence of corner witnesses with levels `eps_k -> 0` needs `diam F_k >= 1/(18 eps_k)`. In
particular, for any family of finite quotients whose Cayley diameters are `O(log |F|)`, a corner of level
`eps` needs `|F| >= exp(c/eps)` for some `c > 0` depending on the family.

**Quantitative forms** (proved in the route).
- (1 => 2) A nontrivial exact pair of defect `D < eps/2` produces an `eps`-corner. The rank of `P` is the
  dimension of the pair.
- (2 => 1) An `eps`-corner with `eps < 1/4` produces a nontrivial exact pair of defect `< 180 eps` and of
  dimension `rank P`.

## Why it matters

- **The finite-quotient class is complete, not dead.** The w19 record
  (`thompson-t-triangle-genuine-rep-relator-gap`, and item 2 of
  `lie-closure-trichotomy-without-finite-quotients`) says a whole representation of `G0` with finite image
  never has defect below `1/2`. Theorem A shows that finite images still carry every MF witness of `T`,
  as almost-invariant corners. The w19 kill is the case `P = 1` of (C1)-(C3).
- **The padding is invisible on the corner.** `thompson-t-padded-cover-stability-is-inert` kills padded
  stability for the *absolute* defect `D(pi)`, which is a maximum over blocks. Read on the corner, the
  same `R_q`-padded correction transfers the witness exactly. (C1) is what the auxiliary block costs, and
  it costs only `O(eps)`.
- **A finitary, group-theoretic form of the target.** `T` is not MF iff there is `c > 0` such that for
  every finite group `F` generated by an element of order dividing 4 and one of order dividing 3, and
  every unitary representation of `F`, no projection is `c`-almost invariant while compressing
  `r_1, r_2, r_P` to within `c` of `1` and a generator to distance `>= 1` from `1`. By Theorem A(3) this
  is a statement about projections in matrix algebras over the group algebras `C[F]`.
- **An invariant for the class.** Theorem B names the invariant: the Cayley diameter. The step where a
  corner dies is the averaging `E(P) = |F|^(-1) sum_g pi(g) P pi(g)^*`. Once `diam F * eps < 1/18`, the
  average rounds to an exactly invariant projection, and the w19 bound `1/2` applies to the resulting
  subrepresentation. So corner witnesses must come from finite quotients whose diameter grows at least
  like `1/eps`, and from families with logarithmic diameter only at exponential size.

## What is left

Theorem A trades the problem for a problem about finite groups; it does not decide it.
- **To refute the target (prove T MF)**, exhibit finite quotients `F_k` of `Z/4 * Z/3` with slow mixing,
  `diam F_k * eps_k >= 1/18`, carrying `eps_k`-corners. A natural test family is the congruence
  quotients `SL(2, Z/q)`, through `G0 ->> SL(2, Z)` with `a -> S` and `b -> -ST`. Here `S` has order 4,
  `-ST` has order 3, and together they generate `SL(2, Z)`. By Selberg's theorem these quotients have
  logarithmic diameter (recalled, not load-bearing), so Theorem B forces exponential size for them.
- **To prove the target**, show a uniform positive corner level. Theorem B reduces this to finite
  quotients of large diameter. A uniform version would need to replace the diameter by a quantity that
  also controls averaging along the relators `r_1, r_2`, which Theorem B does not use.
- **Refinement not made here.** It is open whether `F` may be taken to be a quotient of `Delta(4,3,5)`,
  i.e. with `r_P = 1` exactly in `F`. The same argument would give this from `R_q`-stability of
  `Delta(4,3,5)`, restricted to exact pairs. Willett's Theorem 1.10 concerns surface groups, and only
  conditionally on winding invariants. `Delta(4,3,5)` has torsion, which his Section 1.7 leaves aside,
  and the pentagon winding of `thompson-t-pentagon-winding-sandwich` is exactly such a winding invariant.

## Attempts

- **2026-09-20 (swarm-0917-w20-w20-ptl-follow).** Node created, with Theorems A and B proved in the route.
